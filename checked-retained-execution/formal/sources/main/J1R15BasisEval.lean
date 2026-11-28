import J1R15BitLookup
import J1R14QueryRowMachine

/-! Per-coordinate MAIN exceptional basis multiplication on the serialized
cell and basis fields. Signs are determined by bit comparisons, not supplied
as the already evaluated coefficient of a full row. -/
namespace J1R15
open AOracleMachineTime J1R14Query
open scoped BigOperators

abbrev OrderedBits := List Bool × List Bool

structure BasisBits where
  sides : OrderedBits
  offDiagonal : Bool
  odd : Bool

def pairTest (a b : OrderedBits) : Meter Bool :=
  let first := equalBits a.1 b.1
  let second := equalBits a.2 b.2
  ⟨first.result && second.result,first.steps+second.steps+1⟩

theorem wordEq_result {r : ℕ} (a b : Fin r) :
    (equalBits (finWord a) (finWord b)).result = decide (a=b) := by
  rw [equalBits_result]
  by_cases h : a=b
  · simp [h]
  · have hn : finWord a ≠ finWord b := fun hw => h (finWord_injective r hw)
    simp [h,hn]

def orderedBits {r : ℕ} (a : Fin r × Fin r) : OrderedBits := (finWord a.1,finWord a.2)

theorem pairTest_result {r : ℕ} (a b : Fin r × Fin r) :
    (pairTest (orderedBits a) (orderedBits b)).result = decide (a=b) := by
  rcases a with ⟨a,c⟩
  rcases b with ⟨b,d⟩
  simp only [pairTest,orderedBits,wordEq_result]
  by_cases h₁ : a=b <;> by_cases h₂ : c=d <;> simp [h₁,h₂]

theorem pairTest_cost (a b : OrderedBits) (w : ℕ) (h₁ : a.1.length ≤ w) (h₂ : a.2.length ≤ w) :
    (pairTest a b).steps ≤ 8*w+3 := by
  have ha := (Nat.min_le_left a.1.length b.1.length).trans h₁
  have hb := (Nat.min_le_left a.2.length b.2.length).trans h₂
  simp only [pairTest,equalBits_cost]
  omega

def encodeBasis {r : ℕ} : LocalBasis (Fin r) → BasisBits
  | .inl a => ⟨orderedBits (a,a),false,false⟩
  | .inr (ab,sgn) => ⟨orderedBits ab.val,true,sgn⟩

def runLocal (b : BasisBits) (u : OrderedBits) : Meter SignedUnit :=
  let same := pairTest b.sides u
  let rev := pairTest (b.sides.2,b.sides.1) u
  let v := if same.result then SignedUnit.plus
           else if b.offDiagonal && rev.result then
             if b.odd then SignedUnit.minus else SignedUnit.plus
           else SignedUnit.zero
  ⟨v,same.steps+rev.steps+6⟩

theorem reverseOrdered {r : ℕ} (a : Fin r × Fin r) :
    ((orderedBits a).2,(orderedBits a).1) = orderedBits (a.2,a.1) := rfl

theorem runLocal_amount {r : ℕ} (b : LocalBasis (Fin r)) (u : Fin r × Fin r) :
    (runLocal (encodeBasis b) (orderedBits u)).result.amount = localEntry b u := by
  cases b with
  | inl a =>
    by_cases h : u=(a,a)
    · subst u
      simp [runLocal,encodeBasis,pairTest_result,localEntry,indicatorInt,SignedUnit.amount]
    · simp [runLocal,encodeBasis,pairTest_result,localEntry,indicatorInt,SignedUnit.amount,Ne.symm h,h]
  | inr p =>
    rcases p with ⟨ab,sgn⟩
    have hne : ab.val ≠ (ab.val.2,ab.val.1) :=
      fun he => (ne_of_lt ab.property) (congrArg Prod.fst he)
    by_cases h₁ : u=ab.val
    · subst u
      simp [runLocal,encodeBasis,pairTest_result,localEntry,indicatorInt,SignedUnit.amount,hne]
    · by_cases h₂ : u=(ab.val.2,ab.val.1)
      · subst u
        cases sgn <;>
          norm_num [runLocal,encodeBasis,reverseOrdered,pairTest_result,localEntry,indicatorInt,
            SignedUnit.amount,hne,Ne.symm hne]
      · simp [runLocal,encodeBasis,reverseOrdered,pairTest_result,localEntry,indicatorInt,
          SignedUnit.amount,h₁,h₂,Ne.symm h₁,Ne.symm h₂]

theorem runLocal_cost {r : ℕ} (b : LocalBasis (Fin r)) (u : OrderedBits) :
    (runLocal (encodeBasis b) u).steps ≤ 16*Nat.clog 2 r+12 := by
  have hc : (encodeBasis b).sides.1.length = Nat.clog 2 r ∧
      (encodeBasis b).sides.2.length = Nat.clog 2 r := by
    cases b <;> simp [encodeBasis,orderedBits]
  have e₁ := pairTest_cost (encodeBasis b).sides u (Nat.clog 2 r) hc.1.le hc.2.le
  have e₂ := pairTest_cost ((encodeBasis b).sides.2,(encodeBasis b).sides.1) u
    (Nat.clog 2 r) hc.2.le hc.1.le
  change (pairTest (encodeBasis b).sides u).steps +
    (pairTest ((encodeBasis b).sides.2,(encodeBasis b).sides.1) u).steps+6 ≤ _
  omega

def mulUnit : SignedUnit → SignedUnit → SignedUnit
  | .zero, _ | _, .zero => .zero
  | .plus, r => r
  | .minus, .plus => .minus
  | .minus, .minus => .plus

theorem mulUnit_amount (a b : SignedUnit) : (mulUnit a b).amount = a.amount*b.amount := by
  cases a <;> cases b <;> decide

abbrev BasisRows := List (BasisBits × OrderedBits)

def runBasis : BasisRows → Meter SignedUnit
  | [] => ⟨.plus,1⟩
  | (b,u)::ts =>
    let first := runLocal b u
    let more := runBasis ts
    ⟨mulUnit first.result more.result,first.steps+more.steps+3⟩

theorem runBasis_amount (row : BasisRows) :
    (runBasis row).result.amount = (row.map fun a => (runLocal a.1 a.2).result.amount).prod := by
  induction row with
  | nil => rfl
  | cons a ts ih =>
    rcases a with ⟨b,u⟩
    simp [runBasis,mulUnit_amount,ih]

theorem runBasis_cost (row : BasisRows) (budget : ℕ)
    (h : ∀ x ∈ row, (runLocal x.1 x.2).steps ≤ budget) :
    (runBasis row).steps ≤ row.length*(budget+3)+1 := by
  induction row with
  | nil => simp [runBasis]
  | cons a ts ih =>
    rcases a with ⟨b,u⟩
    have hf := h (b,u) List.mem_cons_self
    have hr := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    change (runLocal b u).steps+(runBasis ts).steps+3 ≤ ((b,u)::ts).length*(budget+3)+1
    calc
      _ ≤ budget + (ts.length*(budget+3)+1)+3 := Nat.add_le_add_right (Nat.add_le_add hf hr) 3
      _ = _ := by simp only [List.length_cons,Nat.succ_mul]; ac_rfl

def fullBasisBits {q r : ℕ} (b : Fin q → LocalBasis (Fin r))
    (u : MainProbe.Cell (Fin q) (Fin r)) : BasisRows :=
  List.ofFn fun i => (encodeBasis (b i),orderedBits (u.1 i,u.2 i))

theorem fullBasis_exact {q r : ℕ} (b : Fin q → LocalBasis (Fin r))
    (u : MainProbe.Cell (Fin q) (Fin r)) :
    (runBasis (fullBasisBits b u)).result.amount = basisEntry b u := by
  rw [runBasis_amount,fullBasisBits,List.map_ofFn,List.prod_ofFn]
  exact Finset.prod_congr rfl fun i _ => runLocal_amount (b i) (u.1 i,u.2 i)

theorem fullBasis_cost {q r : ℕ} (b : Fin q → LocalBasis (Fin r))
    (u : MainProbe.Cell (Fin q) (Fin r)) :
    (runBasis (fullBasisBits b u)).steps ≤ q*(16*Nat.clog 2 r+12+3)+1 := by
  have he := runBasis_cost (fullBasisBits b u) (16*Nat.clog 2 r+12) (by
    intro t ht
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
    exact runLocal_cost (b i) _)
  simpa only [fullBasisBits,List.length_ofFn] using he

#print axioms wordEq_result
#print axioms pairTest_result
#print axioms pairTest_cost
#print axioms runLocal_amount
#print axioms runLocal_cost
#print axioms mulUnit_amount
#print axioms runBasis_amount
#print axioms runBasis_cost
#print axioms fullBasis_exact
#print axioms fullBasis_cost
end J1R15
