import J6R9HermiteRing
import J8EndToEnd

/-! Concrete receipt from the source's localized integers through its
actual mod-2^p receiving ring and canonical integer lifts. -/
namespace J6R9Hermite
open HermiteLoss DenominatorBudget
open J6ActiveSchedule DyadicProbeCompiler NativeProbeRing
open scoped BigOperators

local instance : IsLocalization atTwoPrime.primeCompl TwoLocal := by
  unfold TwoLocal twoLocalSubalgebra
  infer_instance

theorem complement_unit (d : atTwoPrime.primeCompl) :
    IsUnit (algebraMap ℤ Source (d:ℤ)) := by
  have hd : ¬ (2:ℤ)∣(d:ℤ) := by
    simpa only [atTwoPrime,Ideal.mem_primeCompl_iff,Ideal.mem_span_singleton] using d.property
  have ho : Odd (d:ℤ) := Int.not_even_iff_odd.mp (hd ∘ even_iff_two_dvd.mp)
  exact IsLocalization.map_units Source (⟨(d:ℤ),ho⟩:odds)

noncomputable def toNative : TwoLocal→+*Source :=
  IsLocalization.lift (M:=atTwoPrime.primeCompl) (g:=algebraMap ℤ Source) complement_unit

theorem toNative_comp : J8EndToEnd.rationalMap.comp toNative = twoLocalRat := by
  apply IsLocalization.ringHom_ext atTwoPrime.primeCompl
  ext n
  simp only [RingHom.comp_apply]
  rw [show toNative (algebraMap ℤ TwoLocal n) = algebraMap ℤ Source n from
    IsLocalization.lift_eq complement_unit n]
  rw [show J8EndToEnd.rationalMap (algebraMap ℤ Source n) = (n:ℚ) from
    IsLocalization.lift_eq J8EndToEnd.oddRatUnit n,algebraMap_int_eq]
  change (n:ℚ) = twoLocalRat (n:TwoLocal)
  rw [map_intCast]

theorem twoLocal_native_compat (z : TwoLocal) :
    J8EndToEnd.rationalMap (toNative z) = algebraMap ℚ ℚ (twoLocalRat z) := by
  simpa only [RingHom.comp_apply,Algebra.algebraMap_self_apply] using
    RingHom.congr_fun toNative_comp z

theorem canonical_val_receipt (p : ℕ) (x : Base p) :
    coeffReduction p (x.val:Source)=x := by
  haveI : NeZero ((2:ℕ)^p) := ⟨pow_ne_zero _ (by decide)⟩
  rw [map_natCast]
  exact ZMod.natCast_zmod_val x

/-- The actual receiving map gives the used high-precision modular
equality. Canonical lifts are taken only after each right-hand quotient
coefficient is received. -/
theorem finite_native_receive (a M u p : ℕ) (hM : u≤M)
    (truth : ℤ→ℕ→Source) (out : Source)
    (menu : (t : ℤ)→ℕ→Base (childPrecision p a M u t))
    (correct : recompose a M u (fun t j => J8EndToEnd.rationalMap (truth t j)) =
      J8EndToEnd.rationalMap out)
    (receipt : ∀ t∈active a M u, ∀ j<order M u t,
      menu t j=coeffReduction (childPrecision p a M u t) (truth t j)) :
    ∃ z : Source,
      J8EndToEnd.rationalMap z =
        recompose a M u (fun t j => ((menu t j).val:ℚ)) ∧
      coeffReduction p z=coeffReduction p out := by
  let approx (t : ℤ) (j : ℕ) : Source := (menu t j).val
  have data : ∀ t∈active a M u, ∀ j<order M u t,
      (2:Source)^childPrecision p a M u t ∣ approx t j-truth t j := by
    intro t ht j hj
    let P := childPrecision p a M u t
    apply kernel_power_divisibility (coeffReduction P) P (coeffReduction_ker P)
    rw [show coeffReduction P (approx t j)=menu t j from canonical_val_receipt P _]
    exact receipt t ht j hj
  obtain ⟨z,hz,hres⟩ := finite_ring_receive_reduced J8EndToEnd.rationalMap toNative
    twoLocal_native_compat a M u p hM approx truth out correct data
    (coeffReduction p) (base_nilpotent p)
  have hz' : J8EndToEnd.rationalMap z =
      recompose a M u (fun t j => ((menu t j).val:ℚ)) := by
    simpa only [linearRecompose,recompose,smul_eq_mul,approx,map_natCast] using hz
  exact ⟨z,hz',hres⟩

/-- Exact signed integer after an optional public scaling. Never choose an
arbitrary rational representative in a quotient of a characteristic-zero
field. The centered representative is taken after returning to the native
power-of-two residue ring. -/
theorem centered_scaling (p : ℕ) (z out : Source) (D n : ℤ)
    (hres : coeffReduction p z=coeffReduction p out)
    (scale : (D:ℚ)*J8EndToEnd.rationalMap out=(n:ℚ))
    (fits : n*2 ∈ Set.Ioc (-(↑((2:ℕ)^p)) : ℤ) ↑((2:ℕ)^p)) :
    (coeffReduction p ((D:Source)*z)).valMinAbs=n := by
  haveI : NeZero ((2:ℕ)^p) := ⟨pow_ne_zero _ (by decide)⟩
  have he : (D:Source)*out=(n:Source) := by
    apply J8EndToEnd.rationalMap_injective
    simpa only [map_mul,map_intCast] using scale
  rw [map_mul,hres,←map_mul,he,map_intCast]
  exact (ZMod.valMinAbs_spec _ _).mpr ⟨rfl,fits⟩

theorem centered_unscale (p : ℕ) (z out : Source) (D n : ℤ) (hD : D≠0)
    (hres : coeffReduction p z=coeffReduction p out)
    (scale : (D:ℚ)*J8EndToEnd.rationalMap out=(n:ℚ))
    (fits : n*2 ∈ Set.Ioc (-(↑((2:ℕ)^p)) : ℤ) ↑((2:ℕ)^p)) :
    ((coeffReduction p ((D:Source)*z)).valMinAbs:ℚ)/D =
      J8EndToEnd.rationalMap out := by
  rw [centered_scaling p z out D n hres scale fits,←scale]
  exact mul_div_cancel_left₀ _ (by exact_mod_cast hD)

#print axioms toNative_comp
#print axioms finite_native_receive
#print axioms centered_scaling
#print axioms centered_unscale
end J6R9Hermite

