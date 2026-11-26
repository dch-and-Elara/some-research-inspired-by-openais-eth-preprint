import J6R9RecursiveRings
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.Polynomial.GaussLemma

/-! The D1 specialization ell=1 uses the source odd-local extension
embedded into its actual rational field, not a truncated algebra
treated as a field. -/
namespace Paper5.D1Literal
open Polynomial J6R9Recursive

section ZeroCoordinate
variable (A : Type*) [CommRing A]

noncomputable def zeroCoordinate : AdjoinRoot ((X : A[X])^1) →+* A :=
  AdjoinRoot.lift (RingHom.id A) 0 (by simp)

theorem zeroCoordinate_mk (p : A[X]) :
    zeroCoordinate A (AdjoinRoot.mk (X^1) p) = p.eval 0 := by
  unfold zeroCoordinate
  rw [AdjoinRoot.lift_mk, Polynomial.eval₂_id]

theorem zeroCoordinate_injective : Function.Injective (zeroCoordinate A) := by
  have h : Function.LeftInverse (AdjoinRoot.of (X^1)) (zeroCoordinate A) := by
    intro x
    obtain ⟨p,rfl⟩ := AdjoinRoot.mk_surjective x
    rw [zeroCoordinate_mk A]
    change AdjoinRoot.mk (X^1) (C (p.eval 0)) = AdjoinRoot.mk (X^1) p
    apply (AdjoinRoot.mk_eq_mk).mpr
    rw [pow_one, X_dvd_iff, coeff_sub, coeff_C_zero, coeff_zero_eq_eval_zero, sub_self]
  exact h.injective

end ZeroCoordinate

theorem source_rat_irreducible (f : ℤ[X]) (hf : f.Monic)
    (hr : Irreducible (NativeProbeRing.residuePoly f)) :
    Irreducible (ratPoly f) := by
  let r := Int.castRingHom (ZMod 2)
  have hz : Irreducible f := by
    refine ⟨fun hfUnit => hr.not_isUnit (IsUnit.map (mapRingHom r) hfUnit), ?_⟩
    intro a b hab
    have leading : a.leadingCoeff*b.leadingCoeff=1 := by
      rw [← leadingCoeff_mul, ← hab]
      exact hf
    have hmod : NativeProbeRing.residuePoly f=(a.map r)*(b.map r) := by
      change f.map r = _
      rw [hab,Polynomial.map_mul]
    rcases hr.isUnit_or_isUnit hmod with ha | hb
    · exact Or.inl (isUnit_of_isUnit_leadingCoeff_of_isUnit_map r (isUnit_of_mul_eq_one _ _ leading) ha)
    · exact Or.inr (isUnit_of_isUnit_leadingCoeff_of_isUnit_map r
          (isUnit_of_mul_eq_one _ _ ((mul_comm _ _).trans leading)) hb)
  exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hf.isPrimitive).mp hz

noncomputable def sourceFieldMap (f : ℤ[X]) : IntRing f 1 →+* RatScalar f :=
  (zeroCoordinate (RatScalar f)).comp (embed f 1)

theorem sourceFieldMap_injective (f : ℤ[X]) (hf : f.Monic) :
    Function.Injective (sourceFieldMap f) :=
  (zeroCoordinate_injective _).comp (embed_inj f hf 1)

theorem root_congruence_reduces_mod_two (f : ℤ[X]) (hf : f.Monic)
    (ell p : ℕ) (hp : 1≤p) {x y : IntRing f ell}
    (h : (2 : IntRing f ell)^p ∣ x-y) :
    reduce 1 f ell x = reduce 1 f ell y := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (reduce_zero_iff 1 f hf ell _).mpr ((pow_dvd_pow (2:IntRing f ell) hp).trans h)

#print axioms zeroCoordinate_mk
#print axioms zeroCoordinate_injective
#print axioms source_rat_irreducible
#print axioms sourceFieldMap_injective
#print axioms root_congruence_reduces_mod_two
end Paper5.D1Literal

