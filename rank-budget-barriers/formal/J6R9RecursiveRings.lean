import J6ActiveInterpolation
import J6ZeroTransportQuotient
import Mathlib.Tactic

/-! The two polynomial quotients defining the literal integral and
rational Appendix D coefficient algebras. A monic modulus makes both
normal-form operations commute with coefficient maps; this transports
surjectivity, injectivity and the exact ideal (2^p) through both stages. -/
namespace J6R9Recursive
open scoped Polynomial
open Polynomial DenominatorBudget

section Adjoin
variable {A B : Type*} [CommRing A] [CommRing B]

noncomputable def adjoinMap (ψ : A →+* B) (P : A[X]) (Q : B[X])
    (h : P.map ψ = Q) : AdjoinRoot P →+* AdjoinRoot Q :=
  AdjoinRoot.lift ((AdjoinRoot.of Q).comp ψ) (AdjoinRoot.root Q) (by
    rw [← Polynomial.eval₂_map, h]
    exact AdjoinRoot.eval₂_root Q)

theorem adjoinMap_mk (ψ : A →+* B) (P : A[X]) (Q : B[X]) (h : P.map ψ = Q)
    (x : A[X]) :
    adjoinMap ψ P Q h (AdjoinRoot.mk P x) = AdjoinRoot.mk Q (x.map ψ) := by
  rw [adjoinMap, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map]
  exact AdjoinRoot.aeval_eq _

theorem adjoinMap_of (ψ : A →+* B) (P : A[X]) (Q : B[X]) (h : P.map ψ = Q)
    (x : A) :
    adjoinMap ψ P Q h (AdjoinRoot.of P x) = AdjoinRoot.of Q (ψ x) := by
  rw [← AdjoinRoot.mk_C, adjoinMap_mk, Polynomial.map_C, AdjoinRoot.mk_C]

theorem adjoinMap_surj (ψ : A →+* B) (P : A[X]) (Q : B[X]) (h : P.map ψ = Q)
    (hψ : Function.Surjective ψ) : Function.Surjective (adjoinMap ψ P Q h) := by
  intro y
  obtain ⟨b,rfl⟩ := AdjoinRoot.mk_surjective y
  obtain ⟨a,rfl⟩ := Polynomial.map_surjective ψ hψ b
  exact ⟨AdjoinRoot.mk P a,adjoinMap_mk ψ P Q h a⟩

theorem adjoinMap_inj (ψ : A →+* B) (P : A[X]) (Q : B[X]) (h : P.map ψ = Q)
    (hm : P.Monic) (hψ : Function.Injective ψ) : Function.Injective (adjoinMap ψ P Q h) := by
  intro x y e
  obtain ⟨a,rfl⟩ := AdjoinRoot.mk_surjective x
  obtain ⟨b,rfl⟩ := AdjoinRoot.mk_surjective y
  have hmon : Q.Monic := h ▸ hm.map ψ
  have he := congrArg (AdjoinRoot.modByMonicHom hmon) e
  rw [adjoinMap_mk,adjoinMap_mk,AdjoinRoot.modByMonicHom_mk,AdjoinRoot.modByMonicHom_mk,
    ← h, ← Polynomial.map_modByMonic ψ hm, ← Polynomial.map_modByMonic ψ hm] at he
  have he' := congrArg (AdjoinRoot.mk P) (Polynomial.map_injective ψ hψ he)
  calc
    AdjoinRoot.mk P a = AdjoinRoot.mk P (a %ₘ P) := by
      rw [← AdjoinRoot.modByMonicHom_mk hm,AdjoinRoot.mk_leftInverse hm]
    _ = AdjoinRoot.mk P (b %ₘ P) := he'
    _ = _ := by rw [← AdjoinRoot.modByMonicHom_mk hm,AdjoinRoot.mk_leftInverse hm]

theorem adjoinMap_zero_iff (ψ : A →+* B) (P : A[X]) (Q : B[X]) (h : P.map ψ = Q)
    (hm : P.Monic) (d : A) (hψ : ∀ x, ψ x = 0 ↔ d ∣ x) (x : AdjoinRoot P) :
    adjoinMap ψ P Q h x = 0 ↔ (AdjoinRoot.of P d) ∣ x := by
  constructor
  · intro e
    obtain ⟨a,rfl⟩ := AdjoinRoot.mk_surjective x
    have hmon : Q.Monic := h ▸ hm.map ψ
    have he := congrArg (AdjoinRoot.modByMonicHom hmon) e
    rw [adjoinMap_mk,AdjoinRoot.modByMonicHom_mk,map_zero,
      ← h, ← Polynomial.map_modByMonic ψ hm] at he
    have hd : C d ∣ a %ₘ P := by
      apply (C_dvd_iff_dvd_coeff _ _).mpr
      intro j
      apply (hψ _).mp
      simpa only [Polynomial.coeff_map,Polynomial.coeff_zero] using
        congrArg (fun b : B[X] => b.coeff j) he
    rcases hd with ⟨b,hb⟩
    refine ⟨AdjoinRoot.mk P b,?_⟩
    calc
      AdjoinRoot.mk P a = AdjoinRoot.mk P (a %ₘ P) := by
        rw [← AdjoinRoot.modByMonicHom_mk hm,AdjoinRoot.mk_leftInverse hm]
      _ = _ := by rw [hb,map_mul,AdjoinRoot.mk_C]
  · rintro ⟨y,rfl⟩
    rw [map_mul,adjoinMap_of,(hψ d).mpr (dvd_refl d),map_zero,zero_mul]
end Adjoin

noncomputable abbrev intPoly (f : ℤ[X]) := f.map (Int.castRingHom TwoLocal)
noncomputable abbrev ratPoly (f : ℤ[X]) := f.map (Int.castRingHom ℚ)
abbrev IntScalar (f : ℤ[X]) := AdjoinRoot (intPoly f)
abbrev RatScalar (f : ℤ[X]) := AdjoinRoot (ratPoly f)
abbrev IntRing (f : ℤ[X]) (ell : ℕ) := AdjoinRoot ((X : (IntScalar f)[X])^ell)
abbrev RatRing (f : ℤ[X]) (ell : ℕ) := AdjoinRoot ((X : (RatScalar f)[X])^ell)

theorem map_integer_poly {A B : Type*} [CommRing A] [CommRing B] (ψ : A →+* B)
    (f : ℤ[X]) : (f.map (Int.castRingHom A)).map ψ = f.map (Int.castRingHom B) := by
  rw [Polynomial.map_map]
  congr 1
  exact RingHom.ext (fun n => by simp)

noncomputable def embedScalar (f : ℤ[X]) : IntScalar f →+* RatScalar f :=
  adjoinMap twoLocalRat (intPoly f) (ratPoly f) (map_integer_poly _ f)

noncomputable def reduceScalar (p : ℕ) (f : ℤ[X]) :
    IntScalar f →+* NativeProbeRing.Scalar p f :=
  adjoinMap (J6ZeroTransport.reduceBase p) (intPoly f) (NativeProbeRing.liftPoly p f)
    (map_integer_poly _ f)

noncomputable def embed (f : ℤ[X]) (ell : ℕ) : IntRing f ell →+* RatRing f ell :=
  adjoinMap (embedScalar f) _ _ (by simp)

noncomputable def reduce (p : ℕ) (f : ℤ[X]) (ell : ℕ) :
    IntRing f ell →+* J6ActiveInterpolation.Ring p f ell :=
  adjoinMap (reduceScalar p f) _ _ (by simp)

theorem embed_inj (f : ℤ[X]) (hf : f.Monic) (ell : ℕ) :
    Function.Injective (embed f ell) :=
  adjoinMap_inj _ _ _ _ (monic_X.pow _) (adjoinMap_inj _ _ _ _ (hf.map _) twoLocalRat_injective)

theorem reduce_surj (p : ℕ) (f : ℤ[X]) (ell : ℕ) :
    Function.Surjective (reduce p f ell) :=
  adjoinMap_surj _ _ _ _ (adjoinMap_surj _ _ _ _ (J6ZeroTransport.reduceBase_surjective p))

theorem reduce_zero_iff (p : ℕ) (f : ℤ[X]) (hf : f.Monic) (ell : ℕ) (x : IntRing f ell) :
    reduce p f ell x = 0 ↔ (2:IntRing f ell)^p ∣ x := by
  have hS (x : IntScalar f) : reduceScalar p f x = 0 ↔ (2:IntScalar f)^p ∣ x := by
    have h := adjoinMap_zero_iff (J6ZeroTransport.reduceBase p) (intPoly f)
      (NativeProbeRing.liftPoly p f) (map_integer_poly _ f) (hf.map _)
      ((2:TwoLocal)^p) (J6ZeroTransport.reduceBase_zero_iff p) x
    simpa only [reduceScalar,map_pow,map_ofNat] using h
  have h := adjoinMap_zero_iff (reduceScalar p f) (X^ell) (X^ell) (by simp) (monic_X.pow _)
    ((2:IntScalar f)^p) hS x
  simpa only [reduce,map_pow,map_ofNat] using h

noncomputable def localScalar (f : ℤ[X]) (ell : ℕ) : TwoLocal →+* IntRing f ell :=
  (AdjoinRoot.of (X^ell)).comp (AdjoinRoot.of (intPoly f))

theorem embed_localScalar (f : ℤ[X]) (ell : ℕ) (x : TwoLocal) :
    embed f ell (localScalar f ell x) = algebraMap ℚ (RatRing f ell) (twoLocalRat x) := by
  unfold embed embedScalar localScalar
  rw [RingHom.comp_apply,adjoinMap_of,adjoinMap_of]
  rfl

#print axioms adjoinMap_inj
#print axioms adjoinMap_surj
#print axioms adjoinMap_zero_iff
#print axioms embed_inj
#print axioms reduce_surj
#print axioms reduce_zero_iff
#print axioms embed_localScalar
end J6R9Recursive