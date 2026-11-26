import J6R9RecursiveRings

/-! Actual entrywise least-integer representatives in the two monic bases.
This section of reduction is deliberately a function, not a homomorphism.
It is available for every coefficient of the finite divided Taylor jet. -/
namespace J6R9Recursive
open scoped BigOperators Polynomial
open Polynomial DenominatorBudget

noncomputable def polynomialSection {A B : Type*} [CommRing A] [CommRing B]
    (lift : B → A) (P : B[X]) : A[X] :=
  ∑ j ∈ P.support, monomial j (lift (P.coeff j))

theorem polynomialSection_map {A B : Type*} [CommRing A] [CommRing B]
    (ψ : A →+* B) (lift : B → A) (h : ∀ x, ψ (lift x) = x) (P : B[X]) :
    (polynomialSection lift P).map ψ = P := by
  simp only [polynomialSection,Polynomial.map_sum,Polynomial.map_monomial,h]
  exact P.as_sum_support.symm

noncomputable def finiteCoeffLift (p : ℕ) (x : NativeProbeRing.Base p) : TwoLocal :=
  (x.val:TwoLocal)

theorem finiteCoeffLift_spec (p : ℕ) (x : NativeProbeRing.Base p) :
    J6ZeroTransport.reduceBase p (finiteCoeffLift p x) = x := by
  letI : NeZero ((2:ℕ)^p) := ⟨pow_ne_zero _ (by decide)⟩
  rw [finiteCoeffLift,map_natCast,ZMod.natCast_zmod_val]

noncomputable def canonicalScalar (p : ℕ) (f : ℤ[X]) (hf : f.Monic)
    (x : NativeProbeRing.Scalar p f) : IntScalar f :=
  AdjoinRoot.mk (intPoly f)
    (polynomialSection (finiteCoeffLift p)
      (AdjoinRoot.modByMonicHom (hf.map (Int.castRingHom (NativeProbeRing.Base p))) x))

theorem canonicalScalar_spec (p : ℕ) (f : ℤ[X]) (hf : f.Monic)
    (x : NativeProbeRing.Scalar p f) : reduceScalar p f (canonicalScalar p f hf x) = x := by
  unfold canonicalScalar reduceScalar
  rw [adjoinMap_mk,polynomialSection_map]
  · exact AdjoinRoot.mk_leftInverse (hf.map _) x
  · exact finiteCoeffLift_spec p

noncomputable def canonicalLift (p : ℕ) (f : ℤ[X]) (hf : f.Monic)
    (ell : ℕ) (x : J6ActiveInterpolation.Ring p f ell) : IntRing f ell :=
  AdjoinRoot.mk (X^ell) (polynomialSection (canonicalScalar p f hf)
    (AdjoinRoot.modByMonicHom (monic_X.pow ell) x))

theorem canonicalLift_spec (p : ℕ) (f : ℤ[X]) (hf : f.Monic)
    (ell : ℕ) (x : J6ActiveInterpolation.Ring p f ell) :
    reduce p f ell (canonicalLift p f hf ell x) = x := by
  unfold canonicalLift reduce
  rw [adjoinMap_mk,polynomialSection_map]
  · exact AdjoinRoot.mk_leftInverse (monic_X.pow ell) x
  · exact canonicalScalar_spec p f hf

#print axioms polynomialSection_map
#print axioms finiteCoeffLift_spec
#print axioms canonicalScalar_spec
#print axioms canonicalLift_spec
end J6R9Recursive