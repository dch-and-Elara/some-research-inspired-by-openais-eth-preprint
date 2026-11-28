import J6R14SpecializedBoxHalfMode
import J6R14SpecializedBoxNativeTails

/-! The constructive higher polynomial just obtained has the exact
original J9 constant at every eligible occupied row: the named signed
Cauchy coefficient divided by the literal positive odd denominator.
Thus choosing its own divX does not alter the physical compiler's
fixed lowest coefficient or its signed readout. -/
namespace J6R14SpecializedBox
open scoped Polynomial BigOperators Classical
open Polynomial DenominatorBudget P1DyadicGrid P1DyadicGridBridge
open J6R9PacketCoeff J8Physical J8EndToEnd DyadicProbeCompiler

theorem cHatHalf_coeff0 (a : ℕ) (t : ℤ) :
    (cHatHalf a t).coeff 0 = rho a t := by
  simp [cHatHalf,halfFactors,mul_coeff_zero,coeff_zero_prod]

theorem inverseHalf_coeff0 (a p : ℕ) (hp : 0<p) (u : ℤ) (hu : Odd u) :
    (inverseHalf a p u hu).coeff 0 = oddInverse u hu := by
  rw [coeff_zero_eq_eval_zero]
  simp only [inverseHalf,eval_mul,eval_C,eval_finset_sum,eval_pow,eval_neg,eval_X,mul_zero,neg_zero]
  have h : (∑ j ∈ Finset.range p, (0:TwoLocal)^j) = 1 := by
    rw [Finset.sum_eq_single_of_mem 0 (Finset.mem_range.mpr hp)]
    · exact pow_zero 0
    · intro n _ hn
      exact zero_pow hn
  rw [h,mul_one]

theorem modeHalf_coeff0 (a p : ℕ) (hp : 0<p) (t u : ℤ) (hu : Odd u) (b : ℕ) :
    (modeHalf a p t u hu b).coeff 0 = rho a t * (oddInverse u hu)^(b+1) := by
  rw [modeHalf,mul_coeff_zero,cHatHalf_coeff0]
  have h : ((inverseHalf a p u hu)^(b+1)).coeff 0 = (oddInverse u hu)^(b+1) := by
    rw [coeff_zero_eq_eval_zero,eval_pow,← coeff_zero_eq_eval_zero,inverseHalf_coeff0 a p hp]
  rw [h]

theorem rho_at_extreme (a L : ℕ) (hL : L=2^a) (hp : 0<L) (he : Even L) :
    twoLocalRat (rho a ((L:ℤ)-1)) = (J9FactorBounds.kernel L:ℚ) := by
  have hg := printed_grid_at_width a L hL
  have ht : ((L:ℤ)-1) ∈ grid a := by
    rw [hg]
    simp only [printedGrid,Finset.mem_Ico]
    omega
  rw [rho_rat ht,printed_amplitude_integral L (by omega) he]
  unfold derivRatio outerAmplitude derivativeProduct
  rw [cauchy_derivative_eval ht,cauchy_derivative_eval (zero_mem_grid a)]
  simp only [hg,Int.cast_prod,Int.cast_sub,Int.cast_zero]

theorem crossing_zero_oddPart {t : ℤ} {x τ : ℕ} (d : Crossing t x τ 0) :
    d.oddPart = crossingInt t x τ := by
  have hz : d.level=0 := Nat.eq_zero_of_le_zero d.level_le
  simpa only [hz,pow₂,pow_zero,one_mul] using d.exact_int.symm

noncomputable section
variable {Packet R S V G : Type*} {P : V→Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

set_option linter.unusedSectionVars false in
theorem halfMode_const_is_actual_J9 (a p : ℕ) (hp : 0<p) (hW : L=2^a)
    (he : Even L) (hL : 2<L) (s : S) (b : ℕ) (j : TargetPorts d s)
    (hj : j ∈ groupedTargets d s)
    (cross : Crossing ((L:ℤ)-1) (d.seat (j.1.1,j.2)).2.val
      ((d.seat (pinWire d s)).2.val%2) 0) :
    ((modeHalf a p ((L:ℤ)-1) cross.oddPart cross.odd b).map twoLocalToSource.toRingHom).coeff 0 =
      (physicalKernel d s he hL (J9FactorBounds.kernel L) b (fun _ => 0) j).coeff 0 := by
  apply rationalMap_injective
  rw [coeff_map]
  change rationalMap (twoLocalToSource ((modeHalf a p ((L:ℤ)-1) cross.oddPart cross.odd b).coeff 0)) = _
  rw [source_rat_agrees,modeHalf_coeff0 a p hp,map_mul,map_pow,
    rho_at_extreme a L hW (by omega) he,
    constructed_kernel_normalized d s he hL _ _ _ j hj]
  have hD : (cross.oddPart:ℚ) = physicalDenominator d s j := by
    rw [crossing_zero_oddPart,←denominator_cast]
    rfl
  rw [show twoLocalRat (oddInverse cross.oddPart cross.odd) =
    (1:ℚ)/(cross.oddPart:ℚ) by rfl,hD,div_pow,one_pow,mul_one_div]

#print axioms cHatHalf_coeff0
#print axioms inverseHalf_coeff0
#print axioms modeHalf_coeff0
#print axioms rho_at_extreme
#print axioms crossing_zero_oddPart
#print axioms halfMode_const_is_actual_J9
end
end J6R14SpecializedBox
