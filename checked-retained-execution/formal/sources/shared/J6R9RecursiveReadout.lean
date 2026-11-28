import J6R9RecursiveCanonical
import Mathlib.Data.Rat.Lemmas

/-! A specified rational-to-finite readout for the actual coefficient
algebra. Take the unique nested monic normal forms; reduce each
rational coefficient using its reduced odd denominator. This contains
no test of the unknown true output or membership-choice oracle. -/
namespace J6R9Recursive
open scoped BigOperators Polynomial
open Polynomial DenominatorBudget

theorem adjoinMap_normal {A B : Type*} [CommRing A] [CommRing B]
    (ψ : A →+* B) (P : A[X]) (Q : B[X]) (h : P.map ψ = Q) (hm : P.Monic)
    (x : AdjoinRoot P) :
    AdjoinRoot.modByMonicHom (h ▸ hm.map ψ) (adjoinMap ψ P Q h x) =
      (AdjoinRoot.modByMonicHom hm x).map ψ := by
  obtain ⟨y,rfl⟩ := AdjoinRoot.mk_surjective x
  rw [adjoinMap_mk,AdjoinRoot.modByMonicHom_mk,AdjoinRoot.modByMonicHom_mk,
    Polynomial.map_modByMonic ψ hm,h]

theorem polynomialSection_after_map {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (ψ : A →+* B) (θ : A →+* C) (hinj : Function.Injective ψ)
    (project : B → C) (compat : ∀ x, project (ψ x) = θ x) (P : A[X]) :
    polynomialSection project (P.map ψ) = P.map θ := by
  unfold polynomialSection
  rw [support_map_of_injective P hinj]
  simp_rw [Polynomial.coeff_map,compat]
  conv_rhs => rw [P.as_sum_support,Polynomial.map_sum]
  simp only [Polynomial.map_monomial]

noncomputable def rationalIntegral (x : ℚ) : TwoLocal :=
  if h : ¬ (2:ℤ) ∣ (x.den:ℤ) then
    ⟨x,(mem_twoLocal_iff _).mpr ⟨x.num,x.den,h,by simpa using x.num_div_den.symm⟩⟩
  else 0

theorem rationalIntegral_left (x : TwoLocal) : rationalIntegral (twoLocalRat x) = x := by
  have hx : twoLocalRat x ∈ twoLocalSubalgebra := x.property
  obtain ⟨n,d,hodd,he⟩ := (mem_twoLocal_iff _).mp hx
  have hd : ((twoLocalRat x).den:ℤ) ∣ d := by
    rw [he,Rat.intCast_div_eq_divInt]
    exact Rat.den_dvd n d
  unfold rationalIntegral
  rw [dif_pos (fun he' => hodd (he'.trans hd))]
  rfl

noncomputable def rationalScalarRead (p : ℕ) (f : ℤ[X]) (hf : f.Monic) (x : RatScalar f) :
    NativeProbeRing.Scalar p f :=
  AdjoinRoot.mk (NativeProbeRing.liftPoly p f)
    (polynomialSection (fun q => J6ZeroTransport.reduceBase p (rationalIntegral q))
      (AdjoinRoot.modByMonicHom (hf.map (Int.castRingHom ℚ)) x))

theorem rationalScalarRead_exact (p : ℕ) (f : ℤ[X]) (hf : f.Monic) (x : IntScalar f) :
    rationalScalarRead p f hf (embedScalar f x) = reduceScalar p f x := by
  unfold rationalScalarRead embedScalar
  rw [adjoinMap_normal _ _ _ _ (hf.map (Int.castRingHom TwoLocal)),
    polynomialSection_after_map twoLocalRat (J6ZeroTransport.reduceBase p)
      twoLocalRat_injective _ (fun _ => by rw [rationalIntegral_left])]
  unfold reduceScalar
  rw [← adjoinMap_mk,AdjoinRoot.mk_leftInverse (hf.map (Int.castRingHom TwoLocal))]

noncomputable def rationalRead (p : ℕ) (f : ℤ[X]) (hf : f.Monic) (ell : ℕ)
    (x : RatRing f ell) : J6ActiveInterpolation.Ring p f ell :=
  AdjoinRoot.mk (X^ell) (polynomialSection (rationalScalarRead p f hf)
    (AdjoinRoot.modByMonicHom (monic_X.pow ell) x))

theorem rationalRead_exact (p : ℕ) (f : ℤ[X]) (hf : f.Monic) (ell : ℕ) (x : IntRing f ell) :
    rationalRead p f hf ell (embed f ell x) = reduce p f ell x := by
  have hi : Function.Injective (embedScalar f) :=
    adjoinMap_inj _ _ _ _ (hf.map _) twoLocalRat_injective
  unfold rationalRead embed
  rw [adjoinMap_normal _ _ _ _ (monic_X.pow ell),
    polynomialSection_after_map (embedScalar f) (reduceScalar p f) hi _
      (rationalScalarRead_exact p f hf)]
  unfold reduce
  rw [← adjoinMap_mk,AdjoinRoot.mk_leftInverse (monic_X.pow ell)]

#print axioms adjoinMap_normal
#print axioms polynomialSection_after_map
#print axioms rationalIntegral_left
#print axioms rationalScalarRead_exact
#print axioms rationalRead_exact
end J6R9Recursive