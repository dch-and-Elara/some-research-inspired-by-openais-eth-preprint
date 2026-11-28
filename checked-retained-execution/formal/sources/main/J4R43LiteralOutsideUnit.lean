import J4R43LiteralOutsideScalar

/-! Compute the same signed Cauchy ratio using only exact integer
products/divisions and the p-term geometric inverse of its *odd*
denominator. Raw even derivative differences are never inverted. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget J6R9PacketCoeff P1DyadicGrid P1DyadicGridBridge
noncomputable section
set_option maxHeartbeats 3200000
set_option linter.unusedSimpArgs false

def scaledDerivative (a : ℕ) (t : ℤ) : ℤ :=
  (∏ q∈(grid a).erase t,(t-q)) /
    pow₂ (padicValInt 2 (∏ q∈(grid a).erase 0,((0:ℤ)-q)))

theorem scaled_derivative_odd_fraction (a : ℕ) {t : ℤ} (mem : t∈grid a) :
    Odd (scaledDerivative a t) ∧ Odd (scaledDerivative a 0) ∧
      twoLocalRat (rho a t)=(scaledDerivative a t:ℚ)/(scaledDerivative a 0:ℚ) := by
  obtain ⟨k,s,r,hs,hr,hT,h0⟩ := cauchy_derivative_common_content mem
  have hν : padicValInt 2 ((cauchyPolynomial a).derivative.eval 0)=k := by
    rw [h0,valuation_pow₂_mul_odd k hr]
  have hq (x : ℤ) : (pow₂ k*x)/pow₂ k=x := by
    rw [mul_comm]
    exact Int.mul_ediv_cancel x (ne_of_gt (pow₂_pos k))
  have e0 : scaledDerivative a 0=r := by
    unfold scaledDerivative
    rw [←cauchy_derivative_eval (zero_mem_grid a),hν,h0,hq]
  have e1 : scaledDerivative a t=s := by
    unfold scaledDerivative
    rw [←cauchy_derivative_eval (zero_mem_grid a),←cauchy_derivative_eval mem,hν,hT,hq]
  rw [e1,e0,rho_rat mem]
  refine ⟨hs,hr,?_⟩
  unfold derivRatio
  rw [hT,h0,Int.cast_mul,Int.cast_mul,cast_pow₂]
  have e : (2:ℚ)^k≠0 := by positivity
  have ed : (r:ℚ)≠0 := by exact_mod_cast odd_int_ne_zero hr
  field_simp

variable {R : Type} [CommRing R]

/-- Actual scalar in the receiver; uses integers only before the
odds-normalized geometric recurrence from the prior kernel. -/
theorem compute_actual_unit (a : ℕ) {t : ℤ} (mem : t∈grid a)
    (p : ℕ) (nil : (2:R)^p=0) :
    J6ZeroTransport.reduceAt p nil (rho a t) =
      (scaledDerivative a t:R)*J6ZeroTransport.oddReciprocal R p (scaledDerivative a 0) := by
  obtain ⟨_,odd,hFrac⟩ := scaled_derivative_odd_fraction a mem
  apply J6ZeroTransport.reduce_fraction p nil _ _ _ _ hFrac
  exact fun h=> (Int.not_even_iff_odd.mpr odd) (even_iff_two_dvd.mpr h)

theorem derivative_input_width (a : ℕ) {t : ℤ} (mem : t∈grid a) :
    |(cauchyPolynomial a).derivative.eval t|≤(2:ℤ)^((a+1)*(2*2^a-1)) := by
  have hcard : (grid a).card=2*2^a := by
    rw [actual_grid_as_printed, J8Physical.printedGrid,Int.card_Ico]
    omega
  rw [cauchy_derivative_eval mem,Finset.abs_prod]
  calc
    _≤∏ _q∈(grid a).erase t,(2:ℤ)^(a+1) := by
      apply Finset.prod_le_prod
      · intro q _
        exact abs_nonneg _
      · intro q hq
        have d := grid_difference_bounds mem (Finset.mem_erase.mp hq).2
        exact (abs_lt.mpr (by simpa [pow₂] using d)).le
    _ = _ := by rw [Finset.prod_const,Finset.card_erase_of_mem mem,hcard,←pow_mul]

#print axioms scaled_derivative_odd_fraction
#print axioms compute_actual_unit
#print axioms derivative_input_width
end
end J4R43LiteralOutside

