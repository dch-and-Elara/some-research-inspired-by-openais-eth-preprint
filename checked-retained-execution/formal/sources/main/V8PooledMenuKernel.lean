import J6R10RowIdentity
import J6DeformationLocal
import TruncatedProbeMenu

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

namespace V8PooledMenu
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P1DyadicGrid P11FullPacking
open J6R9PacketCoeff J6R9PacketLocal J6R9PacketScopes J6R9PacketChild

/-- The odd-normalized slope of the actual Cauchy factors has a spare
factor two, uniformly on the entire signed mesh. -/
theorem halfSlope_mem {a : ℕ} {t q : ℤ} (ht : t∈grid a) (hq : q∈grid a) (hne : t≠q) :
    ((2:ℚ)^a / ((t:ℚ)-(q:ℚ))) ∈ twoLocalSubalgebra := by
  have hd := sub_ne_zero.mpr hne
  obtain ⟨w,how,he⟩ := integer_odd_factor hd
  have hv := grid_difference_valuation_le ht hq hne
  have hn : ¬ (2:ℤ) ∣ w := fun h => (Int.not_even_iff_odd.mpr how) (even_iff_two_dvd.mpr h)
  apply (mem_twoLocal_iff _).mpr
  refine ⟨(2:ℤ)^(a-padicValInt 2 (t-q)),w,hn,?_⟩
  have hdq : (t:ℚ)-(q:ℚ) ≠ 0 := by exact_mod_cast hd
  have hwq : (w:ℚ) ≠ 0 := by exact_mod_cast odd_int_ne_zero how
  apply (div_eq_div_iff hdq hwq).mpr
  have hq' : (t:ℚ)-(q:ℚ) = (2:ℚ)^(padicValInt 2 (t-q))*(w:ℚ) := by
    change t-q = _ at he
    unfold pow₂ at he
    exact_mod_cast he
  rw [hq', Int.cast_pow, Int.cast_ofNat, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hv]

noncomputable def halfSlope (a : ℕ) (t q : ℤ) : TwoLocal :=
  if h : t∈grid a ∧ q∈grid a ∧ t≠q then
    ⟨(2:ℚ)^a / ((t:ℚ)-(q:ℚ)), halfSlope_mem h.1 h.2.1 h.2.2⟩
  else 0

theorem slope_twice (a : ℕ) (t q : ℤ) :
    J6ActiveLocalFactor.slope a t q = 2 * halfSlope a t q := by
  by_cases h : t∈grid a ∧ q∈grid a ∧ t≠q
  · apply twoLocalRat_injective
    rw [map_mul,map_ofNat,slope_rat h.1 h.2.1 h.2.2,halfSlope,dif_pos h]
    change (2:ℚ)^(a+1) / ((t:ℚ)-(q:ℚ)) = 2 * ((2:ℚ)^a / ((t:ℚ)-(q:ℚ)))
    rw [pow_succ',mul_div_assoc]
  · simp [J6ActiveLocalFactor.slope,halfSlope,h]

noncomputable def normalizedFactors (a : ℕ) (t : ℤ) (s : Finset ℤ) : TwoLocal[X] :=
  ∏ q ∈ s, (1+C (halfSlope a t q)*X)

/-- Coefficients in the explicit indeterminate representing 2z. -/
noncomputable def normalizedW (a : ℕ) (t k : ℤ) : TwoLocal[X] :=
  if k=t then C (rho a t) * normalizedFactors a t ((grid a).erase t) else
    C (rho a t) * C (halfSlope a t k) * X * normalizedFactors a t (((grid a).erase t).erase k)

private theorem normalized_linear (a : ℕ) (t q : ℤ) :
    ((1+C (halfSlope a t q)*X : TwoLocal[X]).comp (C 2*X)) =
      1+C (J6ActiveLocalFactor.slope a t q)*X := by
  simp only [add_comp,one_comp,mul_comp,C_comp,X_comp,slope_twice,map_mul,map_ofNat]
  ring

private theorem normalized_factors_comp (a : ℕ) (t : ℤ) (s : Finset ℤ) :
    (normalizedFactors a t s).comp (C 2*X) = factors a t s := by
  simp only [normalizedFactors,factors,prod_comp,normalized_linear]

theorem normalized_comp (a : ℕ) (t k : ℤ) :
    (normalizedW a t k).comp (C 2*X) = W a t k := by
  by_cases h : k=t
  · rw [normalizedW,if_pos h,W,if_pos h,mul_comp,C_comp,normalized_factors_comp]
    rfl
  · rw [normalizedW,if_neg h,W,if_neg h]
    simp only [mul_comp,C_comp,X_comp,normalized_factors_comp]
    rw [slope_twice,map_mul]
    ring

theorem normalized_eval {R : Type*} [CommRing R] (ψ : TwoLocal →+* R)
    (a : ℕ) (t k : ℤ) (z : R) :
    (normalizedW a t k).eval₂ ψ (2*z) = (W a t k).eval₂ ψ z := by
  rw [← normalized_comp a t k,eval₂_comp]
  simp [show ψ (2:TwoLocal) = 2 from map_ofNat ψ 2]

/-- The same scaled polynomial agrees with the source quotient after
cancellation, including at mesh roots. -/
theorem normalized_printed {a : ℕ} {t k : ℤ} (ht : t∈grid a) (hk : k∈grid a) (z : ℚ) :
    (normalizedW a t k).eval₂ twoLocalRat (2*z) =
      printedW a k ((t:ℚ)+(2:ℚ)^(a+1)*z) :=
  (normalized_eval twoLocalRat a t k z).trans (W_eval_rat ht hk z)

variable {G R : Type*} [LinearOrder G] [CommRing R] {a b : ℕ}

/-- The stronger C4 bound is \(a+1-i\), not merely the ordinary printed
mode weight \(b+1\). This uses the actual normalized signed-grid coefficient. -/
theorem scaled_cross_gain (mask : MaskFamily a b G) (i : Fin a)
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (p : ℕ) (h₂ : (2:R)^p=0) (z : R) (w : Physical a b G) (m : Mode i p mask) :
    (2:R)^(a+1-i.val) ∣ J6R10RowIdentity.scaledRow mask i ht hv p h₂ z w m := by
  classical
  by_cases h : rowBlock mask i w = target mask i m
  · let d := crossingOf ht hv (targeted_row_bit mask i w m h)
    unfold J6R10RowIdentity.scaledRow
    rw [on_target_exact mask i ht hv p h₂ z w m h]
    change (2:R)^(a+1-i.val) ∣ J6R9PacketReceive.mode a p h₂ i.isLt.le d z m.order.val
    unfold J6R9PacketReceive.mode J6R9PacketReceive.leading
    have he : a+1-i.val ≤ a+1-d.level := Nat.sub_le_sub_left d.level_le _
    apply (pow_dvd_pow (2:R) he).trans
    simp only [mul_assoc]
    exact dvd_mul_right _ _
  · rw [J6R10RowIdentity.scaledRow,off_target mask i ht hv p h₂ z w m h,mul_zero]
    exact dvd_zero _

theorem project_cross_zero {R' : Type*} [CommRing R'] (ψ : R →+* R')
    (mask : MaskFamily a b G) (i : Fin a) {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (p : ℕ) (h₂ : (2:R)^p=0) (z : R) (w : Physical a b G) (m : Mode i p mask)
    {q : ℕ} (hq : q ≤ a+1-i.val) (h' : (2:R')^q=0) :
    ψ (J6R10RowIdentity.scaledRow mask i ht hv p h₂ z w m) = 0 := by
  obtain ⟨c,hc⟩ := (pow_dvd_pow (2:R) hq).trans (scaled_cross_gain mask i ht hv p h₂ z w m)
  rw [hc,map_mul,map_pow,map_ofNat,h',zero_mul]

#print axioms halfSlope_mem
#print axioms slope_twice
#print axioms normalized_comp
#print axioms normalized_eval
#print axioms normalized_printed
#print axioms scaled_cross_gain
#print axioms project_cross_zero

end V8PooledMenu
