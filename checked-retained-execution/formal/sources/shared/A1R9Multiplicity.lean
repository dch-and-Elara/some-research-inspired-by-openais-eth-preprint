import A1R9Blocks

/-! Actual multiplicity verification on fixed-width witness tapes:
each mode is counted by walking the guessed per-row selections, then
comparing its explicit counter to the requested exponent word. -/

namespace A1R9
open scoped BigOperators
open AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeMul
open AOracleWitness

def allocationWords {r m : ℕ} (b : ℕ) (a : Allocation r m) : List (List Bool) :=
  List.ofFn (fun j => encodeBits b (a j).val)

theorem choice_iff_index {m : ℕ} (u : Fin (m+1)) (k : Fin m) :
    choice u=some k ↔ u=k.succ := by
  refine Fin.cases ?_ (fun j => ?_) u
  · simp [choice_zero, Ne.symm (Fin.succ_ne_zero k)]
  · simp [choice_succ]

theorem countP_as_sum {A : Type*} (xs : List A) (b : A → Bool) :
    xs.countP b=(xs.map (fun x => if b x then (1:ℕ) else 0)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hb : b x <;> simp [hb,ih,Nat.add_comm]

theorem allocation_count {r m : ℕ} (a : Allocation r m) (k : Fin m) (b : ℕ)
    (fit : m+1≤2^b) :
    (allocationWords b a).countP (fun u => decide
      (bitsValue (encodeBits b k.succ.val)=bitsValue u))=rowCount a k := by
  unfold allocationWords rowCount
  rw [countP_as_sum]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [encodeBits_exact b k.succ.val (k.succ.isLt.trans_le fit),
    encodeBits_exact b (a j).val ((a j).isLt.trans_le fit)]
  by_cases h : a j=k.succ
  · have h' : k.succ.val=(a j).val := congrArg (fun z : Fin (m+1) => z.val) h.symm
    simp only [h',decide_true,if_true,choice_iff_index,h]
  · have h' : k.succ.val≠(a j).val := fun e => h (Fin.ext e.symm)
    simp only [h',decide_false,Bool.false_eq_true,if_false,choice_iff_index,h]

def checkCounter (q : ℕ) (alloc : List (List Bool)) (key expected : List Bool) : Meter Bool :=
  let n := countWord q key alloc
  let e := eqWord n.result expected
  ⟨e.result,n.steps+e.steps+2⟩

def counterBudget (r b q : ℕ) : ℕ := q+r*(10*b+12*q+6)+10*q+2

theorem checkCounter_exact {r m : ℕ} (a : Allocation r m) (k : Fin m) (expected b q : ℕ)
    (hq : 0<q) (fit : m+1≤2^b) (hrows : r<2^q) (he : expected<2^q) :
    let u := checkCounter q (allocationWords b a) (encodeBits b k.succ.val) (encodeBits q expected)
    (u.result=true ↔ rowCount a k=expected) ∧ u.steps≤counterBudget r b q := by
  let field := encodeBits b k.succ.val
  let alloc := allocationWords b a
  have hlen : alloc.length=r := List.length_ofFn
  have phases (l : List Bool) (hl : l∈alloc) : l.length=field.length := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hl
    simp [field,encodeBits_length]
  let n := countWord q field alloc
  have hi := countWord_exact q field alloc hq (hlen ▸ hrows) phases
  change n.result.length=q ∧ _ ∧ n.steps≤_ at hi
  obtain ⟨hn,hv,hc⟩ := hi
  have hcount : bitsValue n.result = rowCount a k := hv.trans (allocation_count a k b fit)
  obtain ⟨hcomp,htime⟩ := eqWord_exact n.result (encodeBits q expected)
    (hn.trans (encodeBits_length q expected).symm)
  change (eqWord n.result (encodeBits q expected)).result=true ↔
    bitsValue n.result=bitsValue (encodeBits q expected) at hcomp
  refine ⟨?_,?_⟩
  · change ((eqWord n.result (encodeBits q expected)).result=true ↔ _)
    rw [hcomp,hcount,encodeBits_exact q expected he]
  change n.steps+(eqWord n.result (encodeBits q expected)).steps+2≤_
  rw [htime,hn]
  unfold counterBudget
  have f : field.length=b := encodeBits_length _ _
  rw [f,hlen] at hc
  omega

def checkModes (q : ℕ) (alloc : List (List Bool)) : List (List Bool × List Bool) → Meter Bool
  | [] => ⟨true,0⟩
  | (key,w)::ts =>
    let t := checkCounter q alloc key w
    let tail := checkModes q alloc ts
    ⟨t.result && tail.result,t.steps+tail.steps+2⟩

def counterTape {m : ℕ} (b q : ℕ) (beta : Fin m →₀ ℕ) (ks : List (Fin m)) :
    List (List Bool × List Bool) :=
  ks.map (fun k => (encodeBits b k.succ.val,encodeBits q (beta k)))

theorem checkModes_exact {r m : ℕ} (a : Allocation r m) (beta : Fin m →₀ ℕ) (b q : ℕ)
    (hq : 0<q) (fit : m+1≤2^b) (hrows : r<2^q) (hb : ∀ k, beta k<2^q)
    (ks : List (Fin m)) :
    let u := checkModes q (allocationWords b a) (counterTape b q beta ks)
    (u.result=true ↔ ∀ k∈ks, rowCount a k=beta k) ∧
      u.steps≤ks.length*(counterBudget r b q+2) := by
  induction ks with
  | nil => simp [counterTape,checkModes]
  | cons k ks ih =>
    obtain ⟨h₁,h₂⟩ := checkCounter_exact a k (beta k) b q hq fit hrows (hb k)
    obtain ⟨i₁,i₂⟩ := ih
    let head := checkCounter q (allocationWords b a) (encodeBits b k.succ.val) (encodeBits q (beta k))
    let tail := checkModes q (allocationWords b a) (counterTape b q beta ks)
    change (head.result=true ↔ _) at h₁
    change head.steps≤_ at h₂
    change (tail.result=true ↔ _) at i₁
    change tail.steps≤_ at i₂
    change ((head.result && tail.result)=true ↔ ∀ j∈k::ks, rowCount a j=beta j) ∧
      head.steps+tail.steps+2≤(ks.length+1)*(counterBudget r b q+2)
    refine ⟨by simp [h₁,i₁],?_⟩
    rw [Nat.succ_mul ks.length (counterBudget r b q+2)]
    omega

def checkMultiplicity {m : ℕ} (b q : ℕ) (beta : Fin m →₀ ℕ) (alloc : List (List Bool)) : Meter Bool :=
  checkModes q alloc (counterTape b q beta (List.finRange m))

theorem checkMultiplicity_exact {r m : ℕ} (a : Allocation r m)
    (beta : Fin m →₀ ℕ) (b q : ℕ) (hq : 0<q) (fit : m+1≤2^b)
    (hrows : r<2^q) (hb : ∀ k, beta k<2^q) :
    let u := checkMultiplicity b q beta (allocationWords b a)
    (u.result=true ↔ ∀ k, rowCount a k=beta k) ∧
      u.steps≤m*(counterBudget r b q+2) := by
  simpa [checkMultiplicity] using checkModes_exact a beta b q hq fit hrows hb (List.finRange m)

#print axioms choice_iff_index
#print axioms allocation_count
#print axioms checkCounter_exact
#print axioms checkMultiplicity_exact
end A1R9
