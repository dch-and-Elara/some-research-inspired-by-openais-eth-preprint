import A1R9Blocks

/-! The selected scalar nonzero-mode branch on literal coefficient
bits. A crossing coefficient is multiplied by its current source moment;
the sign and target gate are separately verified. This file does not
compute the coefficient tape from Cauchy data. -/

namespace A1R9
open AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeMul
open AOracleMachineTimeLocal AOracleMachineTimeZero AOracleSuccinct AOracleWitness

abbrev LinearTape := List (List Bool × List Bool)

inductive PickTape where
  | affine (recipe : LinearTape)
  | mode (legal : Bool) (cross : List Bool) (moment : LinearTape)

def linearPayload (xs : LinearTape) : ℕ :=
  (xs.map (fun z => z.1.length+z.2.length+2)).sum

theorem packLinear_payload {c p : ℕ} (b : ℕ) (x : Linear c (ZMod (2^p))) :
    linearPayload (packLinear b p x)=x.length*(b+p+2) := by
  induction x with
  | nil => simp [linearPayload,packLinear]
  | cons z xs ih =>
    change (encodeBits b z.1.val).length+(residueWord p z.2).length+2+
      linearPayload (packLinear b p xs)=(xs.length+1)*(b+p+2)
    rw [encodeBits_length,residueWord_length,ih,Nat.succ_mul xs.length (b+p+2)]
    omega

def pickPayload : PickTape → ℕ
  | .affine r => linearPayload r+2
  | .mode _ w r => linearPayload r+w.length+3

def pickAt {r c m delta p : ℕ} (bc : ℕ)
    (L : Recipes (ZMod (2^p)) r c m delta) (j : Fin r) (a : Fin (m+1)) : PickTape :=
  match choice a with
  | none => .affine (packLinear bc p (L.localRecipe j))
  | some k => .mode (L.target j k) (residueWord p (L.cross j k)) (packLinear bc p (L.moment k))

def pickTape {r c m delta p : ℕ} (bc : ℕ)
    (L : Recipes (ZMod (2^p)) r c m delta) (j : Fin r) : List PickTape :=
  List.ofFn (pickAt bc L j)

theorem pickAt_payload {r c m delta p : ℕ} (bc s : ℕ)
    (L : Recipes (ZMod (2^p)) r c m delta) (j : Fin r) (a : Fin (m+1))
    (hL : ∀ j, (L.localRecipe j).length≤s) (hM : ∀ k, (L.moment k).length≤s) :
    pickPayload (pickAt bc L j a) ≤ s*(bc+p+2)+p+3 := by
  unfold pickAt
  cases h : choice a with
  | none =>
    simp only [pickPayload, packLinear_payload]
    have h := Nat.mul_le_mul_right (bc+p+2) (hL j)
    omega
  | some k =>
    simp only [pickPayload,packLinear_payload,residueWord_length]
    have h := Nat.mul_le_mul_right (bc+p+2) (hM k)
    omega

def adjust (p : ℕ) (row isMode : Bool) (w : List Bool) : Meter (List Bool) :=
  if row then Meter.pure w else if isMode then negWord p w else oneSub p w

theorem adjust_exact (p : ℕ) (hp : 0<p) (row isMode : Bool) (w : List Bool) (hw : w.length=p) :
    (adjust p row isMode w).result.length=p ∧
    asResidue p (adjust p row isMode w).result=
      (if row then asResidue p w else if isMode then -asResidue p w else 1-asResidue p w) ∧
    (adjust p row isMode w).steps≤15*p := by
  cases row
  · cases isMode
    · obtain ⟨h₁,h₂,h₃⟩ := oneSub_exact p hp w hw
      exact ⟨h₁,h₂,h₃.le⟩
    · obtain ⟨h₁,h₂,h₃⟩ := negWord_exact p hp w hw
      exact ⟨h₁,h₂,h₃.le⟩
  · exact ⟨hw,rfl,Nat.zero_le _⟩

def runPick (p : ℕ) (x : List Bool) (y : Bool) : PickTape → Meter (Bool × List Bool)
  | .affine recipe =>
    let a := runLinear p x recipe
    let r := adjust p y false a.result
    ⟨(true,r.result),a.steps+r.steps+4⟩
  | .mode leg cr recipe =>
    if leg then
      let a := runLinear p x recipe
      let t := multiply cr a.result
      let r := adjust p y true t.result
      ⟨(true,r.result),a.steps+t.steps+r.steps+4⟩
    else ⟨(false,List.replicate p false),p+4⟩

def pickedBudget (c bc p s : ℕ) : ℕ :=
  p+s*((10*bc+4)*c+12*p+4)+16*(p+1)^2+15*p+4

theorem runPick_at {r c m delta p : ℕ} (bc s : ℕ) (hp : 0<p) (hfit : c≤2^bc)
    (L : Recipes (ZMod (2^p)) r c m delta) (w : Witness r c m) (j : Fin r)
    (hL : ∀ j, (L.localRecipe j).length≤s) (hM : ∀ k, (L.moment k).length≤s) :
    let u := runPick p (List.ofFn w.2.1) (w.1 j) (pickAt bc L j (w.2.2 j))
    u.result.1=allowed (rootTerms L) w.2.2 j ∧
    u.result.2.length=p ∧ asResidue p u.result.2=evaluateRow L w j ∧
    u.steps≤pickedBudget c bc p s := by
  dsimp only
  unfold pickAt evaluateRow allowed
  cases hm : choice (w.2.2 j) with
  | none =>
    let a := runLinear p (List.ofFn w.2.1) (packLinear bc p (L.localRecipe j))
    obtain ⟨al,av,ac⟩ := runLinear_exact w.2.1 bc p (L.localRecipe j) hfit
    change a.result.length=p at al
    change asResidue p a.result=_ at av
    change a.steps≤_ at ac
    obtain ⟨rl,rv,rc⟩ := adjust_exact p hp (w.1 j) false a.result al
    have htime := Nat.mul_le_mul_right ((10*bc+4)*c+12*p+4) (hL j)
    refine ⟨rfl,rl,?_,?_⟩
    · change asResidue p (adjust p (w.1 j) false a.result).result=_
      simp only [rv,av,Bool.false_eq_true,if_false]
    · change a.steps+(adjust p (w.1 j) false a.result).steps+4≤pickedBudget c bc p s
      unfold pickedBudget
      omega
  | some k =>
    simp only [Option.elim_some,rootTerms]
    cases ht : L.target j k with
    | false =>
      simp [runPick,asResidue,value_zero]
      unfold pickedBudget
      omega
    | true =>
      let a := runLinear p (List.ofFn w.2.1) (packLinear bc p (L.moment k))
      let cr := residueWord p (L.cross j k)
      let t := multiply cr a.result
      obtain ⟨al,av,ac⟩ := runLinear_exact w.2.1 bc p (L.moment k) hfit
      change a.result.length=p at al
      change asResidue p a.result=_ at av
      change a.steps≤_ at ac
      have hl : cr.length=p := residueWord_length _ _
      obtain ⟨tl,tv,_⟩ := multiply_result p cr a.result hl
      have tc := square_word_cost p cr a.result hl al
      change t.result.length=p at tl
      change asResidue p t.result=asResidue p cr*asResidue p a.result at tv
      change t.steps≤_ at tc
      obtain ⟨rl,rv,rc⟩ := adjust_exact p hp (w.1 j) true t.result tl
      have crv : asResidue p cr=L.cross j k := residueWord_correct _ _
      have htime := Nat.mul_le_mul_right ((10*bc+4)*c+12*p+4) (hM k)
      refine ⟨rfl,rl,?_,?_⟩
      · change asResidue p (adjust p (w.1 j) true t.result).result=_
        simp only [rv,tv,av,crv,if_true,zero_sub]
      · change a.steps+t.steps+(adjust p (w.1 j) true t.result).steps+4≤pickedBudget c bc p s
        unfold pickedBudget
        omega

#print axioms packLinear_payload
#print axioms pickAt_payload
#print axioms adjust_exact
#print axioms runPick_at
end A1R9
