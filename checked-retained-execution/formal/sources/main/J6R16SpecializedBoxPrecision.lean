import J6R14SpecializedBoxHalfMode

/-! Degree-zero inverse truncation commutes with lowering a receiving
precision. At a genuine unit-denominator crossing the omitted extra
geometric terms vanish already in the lower Box. No dyadic division
is used at any precision. -/
namespace J6R14SpecializedBox
open scoped Polynomial BigOperators Classical
open Polynomial DenominatorBudget
noncomputable section
set_option linter.unusedSectionVars false

variable {K : Type*} [CommRing K]

private theorem geom_range_nil (x : K) {p q : ℕ} (h : p≤q) (hx : x^p=0) :
    (∑ j ∈ Finset.range q, x^j) = ∑ j ∈ Finset.range p, x^j := by
  nth_rw 1 [← Nat.add_sub_of_le h]
  rw [Finset.sum_range_add]
  simp only [pow_add,hx,zero_mul,Finset.sum_const_zero,add_zero]

theorem inverseHalf_lower_precision
    (a p q : ℕ) (hpq : p≤q) (hnil : (2:K)^p=0)
    (u : ℤ) (hu : Odd u) (φ : TwoLocal→+*K) (z : K) :
    (inverseHalf a q u hu).eval₂ φ (2*z) = (inverseHalf a p u hu).eval₂ φ (2*z) := by
  let E := Polynomial.eval₂RingHom φ (2*z)
  let term := -(C (2:TwoLocal)^a * C (oddInverse u hu)*X)
  have hTerm : E term = (2:K)*(-((2:K)^a * φ (oddInverse u hu)*z)) := by
    change term.eval₂ φ (2*z) = _
    simp only [term,eval₂_neg,eval₂_mul,eval₂_pow,eval₂_C,eval₂_X,map_ofNat,eval₂_ofNat]
    ring
  have hNil : (E term)^p=0 := by rw [hTerm,mul_pow,hnil,zero_mul]
  change E (inverseHalf a q u hu) = E (inverseHalf a p u hu)
  simp only [inverseHalf,map_mul,map_sum,map_pow]
  exact congrArg (fun x : K => E (C (oddInverse u hu))*x) (geom_range_nil (E term) hpq hNil)

theorem modeHalf_lower_precision
    (a p q : ℕ) (hpq : p≤q) (hnil : (2:K)^p=0)
    (t u : ℤ) (hu : Odd u) (n : ℕ) (φ : TwoLocal→+*K) (z : K) :
    (modeHalf a q t u hu n).eval₂ φ (2*z) = (modeHalf a p t u hu n).eval₂ φ (2*z) := by
  simp only [modeHalf,eval₂_mul,eval₂_pow,inverseHalf_lower_precision a p q hpq hnil u hu φ z]

#print axioms inverseHalf_lower_precision
#print axioms modeHalf_lower_precision
end
end J6R14SpecializedBox