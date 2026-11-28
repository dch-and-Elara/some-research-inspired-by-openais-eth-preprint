import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! The actual ± tensor swap characters on one unordered-label orbit.
The norm scaling is explicit over the reals; source coefficients remain
integer signs. -/
namespace P5MainIterator
open scoped BigOperators Classical

variable {I : Type*} [Fintype I]

def sign (a b : Bool) : ℝ := if a && b then -1 else 1

noncomputable def walsh (a w : I → Bool) : ℝ := ∏ i, sign (a i) (w i)

theorem sign_square (a b : Bool) : (sign a b)^2=1 := by
  cases a <;> cases b <;> norm_num [sign]

theorem walsh_square (a w : I → Bool) : (walsh a w)^2=1 := by
  unfold walsh
  rw [←Finset.prod_pow]
  simp [sign_square]

theorem sign_product_two (a b : Bool) :
    (∑ w : Bool, sign a w * sign b w) = if a=b then (2:ℝ) else 0 := by
  cases a <;> cases b <;> norm_num [sign,Fintype.sum_bool]

set_option maxHeartbeats 3000000 in
theorem walsh_orthogonal (a b : I → Bool) :
    (∑ w : I → Bool, walsh a w * walsh b w) =
      if a=b then (2:ℝ)^Fintype.card I else 0 := by
  classical
  have hprod :
      (∑ w : I → Bool, ∏ i, sign (a i) (w i) * sign (b i) (w i)) =
        ∏ i, ∑ w : Bool, sign (a i) w * sign (b i) w := by
    rw [Finset.prod_univ_sum,Fintype.piFinset_univ]
  simp only [walsh,← Finset.prod_mul_distrib]
  rw [hprod]
  simp only [sign_product_two]
  by_cases hab : a=b
  · subst b
    simp
  · rw [if_neg hab]
    have hne : ∃ i, a i≠b i := by
      by_contra! h
      exact hab (funext h)
    obtain ⟨i,hi⟩ := hne
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

noncomputable def normalizedWalsh (a w : I → Bool) : ℝ :=
  (Real.sqrt ((2:ℝ)^Fintype.card I))⁻¹ * walsh a w

theorem normalizedWalsh_square (a w : I → Bool) :
    (normalizedWalsh a w)^2 = ((2:ℝ)^Fintype.card I)⁻¹ := by
  unfold normalizedWalsh
  rw [mul_pow,walsh_square,mul_one,inv_pow,Real.sq_sqrt (by positivity)]

theorem normalizedWalsh_orthogonal (a b : I → Bool) :
    (∑ w : I → Bool, normalizedWalsh a w * normalizedWalsh b w) =
      if a=b then (1:ℝ) else 0 := by
  let S := (Real.sqrt ((2:ℝ)^Fintype.card I))⁻¹
  have hh : (∑ w : I → Bool, normalizedWalsh a w * normalizedWalsh b w) =
      S^2 * (∑ w : I → Bool, walsh a w * walsh b w) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    change (S*walsh a w)*(S*walsh b w)=S^2*(walsh a w*walsh b w)
    ring
  rw [hh,walsh_orthogonal]
  have hs : S^2 = ((2:ℝ)^Fintype.card I)⁻¹ := by
    unfold S
    rw [inv_pow,Real.sq_sqrt (by positivity)]
  by_cases hab : a=b
  · rw [if_pos hab,if_pos hab,hs]
    exact inv_mul_cancel₀ (by positivity)
  · rw [if_neg hab,if_neg hab,mul_zero]

#print axioms walsh_square
#print axioms walsh_orthogonal
#print axioms normalizedWalsh_square
#print axioms normalizedWalsh_orthogonal
end P5MainIterator
