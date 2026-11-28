import J6R10RepackRounded
import A1R12Words

/-! Exact power-of-two packet rounding on the load word: quotient is a
suffix, and a nonzero discarded prefix triggers one ripple increment.
This is the printed ceiling, not an estimate of the maximum load. -/

namespace J6R14LayoutCost
open AOracleMachineTime AOracleMachineTimeTape A1R12 P11FullPacking

theorem drop_value (a : ℕ) (xs : List Bool) :
    bitsValue (xs.drop a)=bitsValue xs/2^a := by
  induction a generalizing xs with
  | zero => simp
  | succ a ih =>
    cases xs with
    | nil => simp [bitsValue]
    | cons x xs =>
      have hx : x.toNat≤1 := by cases x <;> decide
      simp only [List.drop_succ_cons,bitsValue,pow_succ,ih]
      rw [Nat.mul_comm (2^a) 2,← Nat.div_div_eq_div_mul]
      rw [show (x.toNat+2*bitsValue xs)/2=bitsValue xs by omega]

theorem take_value (a : ℕ) (xs : List Bool) :
    bitsValue (xs.take a)=bitsValue xs%2^a := by
  have h : bitsValue (xs.take a)=bitsValue (lowBits a xs) := by
    induction a generalizing xs with
    | zero => rfl
    | succ a ih =>
      cases xs with
      | nil => simp [lowBits,bitsValue,← ih []]
      | cons x xs => simp [lowBits,bitsValue,← ih xs]
  exact h.trans (lowBits_value a xs)

def nonzero : List Bool → Meter Bool
  | [] => ⟨false,0⟩
  | b::bs =>
    let t := nonzero bs
    ⟨b || t.result,t.steps+4⟩

theorem nonzero_exact (xs : List Bool) :
    ((nonzero xs).result=true ↔ bitsValue xs≠0) ∧ (nonzero xs).steps=4*xs.length := by
  induction xs with
  | nil => simp [nonzero,bitsValue]
  | cons x xs ih =>
    obtain ⟨hv,hc⟩ := ih
    constructor
    · simp only [nonzero,Bool.or_eq_true,hv,bitsValue]
      cases x <;> simp
    · simp only [nonzero,hc,List.length_cons,Nat.mul_succ]

def roundCap (a q : ℕ) : ℕ := 64*(a+q+3)

def roundLoad (a q : ℕ) (h : List Bool) : Meter (List Bool) :=
  let t := nonzero (h.take a)
  let r := lowBits (q+1) (h.drop a)
  let v := if t.result then addBits r (encodeBits (q+1) 1) else Meter.pure r
  ⟨v.result,t.steps+v.steps+8*(a+q+3)⟩

theorem roundLoad_exact (a q : ℕ) (h : List Bool) (w : h.length=q) :
    (roundLoad a q h).result.length=q+1 ∧
    bitsValue (roundLoad a q h).result=ceilCopies (2^a) (bitsValue h) ∧
    (roundLoad a q h).steps≤roundCap a q := by
  let t := nonzero (h.take a)
  let r := lowBits (q+1) (h.drop a)
  obtain ⟨ht,hc⟩ := nonzero_exact (h.take a)
  change (t.result=true ↔ _) at ht
  change t.steps=_ at hc
  have hm : bitsValue h<2^q := by rw [← w]; exact bitsValue_lt _
  have ht' : t.steps≤4*q := by
    rw [hc,← w]
    exact Nat.mul_le_mul_left _ (by simp)
  have hdiv := Nat.div_le_self (bitsValue h) (2^a)
  have hfit : bitsValue h/2^a+1<2^(q+1) := by rw [pow_succ]; omega
  have hR : r.length=q+1 := lowBits_len _ _
  have hr : bitsValue r=bitsValue h/2^a := by
    rw [show bitsValue r=_ from lowBits_value _ _,drop_value,Nat.mod_eq_of_lt (by omega)]
  rw [take_value] at ht
  have add := addBits_exact r (encodeBits (q+1) 1) (hR.trans (encodeBits_length _ _).symm)
  change (if t.result then addBits r (encodeBits (q+1) 1) else Meter.pure r).result.length=q+1 ∧
    bitsValue (if t.result then addBits r (encodeBits (q+1) 1) else Meter.pure r).result= _ ∧
    t.steps+(if t.result then addBits r (encodeBits (q+1) 1) else Meter.pure r).steps+8*(a+q+3)≤_
  by_cases H : bitsValue h%2^a=0
  · have hc' : t.result=false := Bool.eq_false_iff.mpr (fun hh => (ht.mp hh) H)
    simp only [hc',Bool.false_eq_true,if_false,Meter.pure,hR,hr,ceilCopies,H,if_true,Nat.add_zero,
      true_and]
    unfold roundCap
    omega
  · rw [if_pos (ht.mpr H)]
    refine ⟨add.1.trans hR,?_,?_⟩
    · rw [add.2.1,hr,encodeBits_exact _ _ (one_lt_pow₀ (by decide) (by omega)),hR,
        Nat.mod_eq_of_lt hfit,ceilCopies,if_neg H]
    · rw [add.2.2,hR]
      unfold roundCap
      omega

#print axioms take_value
#print axioms nonzero_exact
#print axioms roundLoad_exact
end J6R14LayoutCost

