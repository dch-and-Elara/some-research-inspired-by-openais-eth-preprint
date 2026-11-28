import NativeProbeRing
import DyadicSlotCompiler
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Nilpotent.Basic

/-! The original odd-denominator coefficient map into the finite
precision extension, and the end-to-end concrete interpolation step. -/

namespace DyadicProbeCompiler
open scoped BigOperators Polynomial
open NativeProbeRing LiteralPortCompiler

def odds : Submonoid ℤ where
  carrier := {x | Odd x}
  one_mem' := odd_one
  mul_mem' := Odd.mul

abbrev Source := Localization odds

theorem odd_unit (p : ℕ) (a : odds) : IsUnit ((a : ℤ) : Base p) := by
  obtain ⟨k, hk⟩ := a.property
  rw [hk]
  push_cast
  have hnil : IsNilpotent ((2 : Base p) * (k : Base p)) := by
    refine ⟨p, ?_⟩
    rw [mul_pow, base_nilpotent, zero_mul]
  exact hnil.isUnit_add_one

noncomputable def coeffReduction (p : ℕ) : Source →+* Base p :=
  IsLocalization.lift (M := odds) (g := Int.castRingHom (Base p)) (odd_unit p)

noncomputable def toScalar (p : ℕ) (f : ℤ[X]) : Source →+* Scalar p f :=
  (AdjoinRoot.of (liftPoly p f)).comp (coeffReduction p)

theorem coeffReduction_int (p : ℕ) (a : ℤ) :
    coeffReduction p (algebraMap ℤ Source a) = (a : Base p) :=
  IsLocalization.lift_eq (odd_unit p) a

theorem coeffReduction_fraction (p : ℕ) (n : ℤ) (u : odds) :
    coeffReduction p (IsLocalization.mk' Source n u) * ((u : ℤ) : Base p) =
      (n : Base p) := by
  rw [mul_comm]
  exact ((IsLocalization.lift_mk'_spec (odd_unit p) n
    (coeffReduction p (IsLocalization.mk' Source n u)) u).mp rfl).symm

/-- J8 readout for the actual quotient polynomial and actual binary probe
family. Includes the nilpotence and unit-spacing proofs; layout data and
normalized row kernels are the remaining upstream inputs. -/
theorem decode_source {P M : Type*} [Fintype P] [DecidableEq P] [Fintype M] [DecidableEq M]
    (prec : ℕ) (hp : 0 < prec) (f : ℤ[X]) (hf : f.Monic)
    (hd : 0 < f.natDegree) [Fact (Irreducible (residuePoly f))]
    (fit : prec+1 ≤ 2^f.natDegree)
    (F : CNF P) (base : (P → Bool) → P → Source[X])
    (kernel : (P → Bool) → P → M → Source[X])
    (e : M → ℕ) (m : M) (hv : 1 ≤ e m) :
    let φ := toScalar prec f
    let x := fun i => probe prec f (chosenRep f.natDegree (prec+1) fit i)
    let β := Finsupp.single m 1
    let q := MvPolynomial.coeff β (completed F base kernel)
    let samples := fun i => MvPolynomial.coeff β
      (completed F (fun a p => (base a p).eval₂ φ (2*x i))
        (fun a p j => (2 : Scalar prec f)^e j * x i * (kernel a p j).eval₂ φ (2*x i)))
    NativeInterpolation.decode x samples ⟨1, by omega⟩ =
      (2 : Scalar prec f)^e m * φ (q.coeff 0) :=
  DyadicSlotCompiler.decode_compiled_singleton (toScalar prec f) prec hp
    (scalar_nilpotent prec f) F base kernel e m hv _
    (chosenProbes_units prec hp f hf hd (prec+1) fit)

theorem coeffReduction_surjective (p : ℕ) :
    Function.Surjective (coeffReduction p) := by
  haveI : NeZero (2^p : ℕ) := ⟨pow_ne_zero _ (by decide)⟩
  intro y
  refine ⟨algebraMap ℤ Source (y.val : ℤ), ?_⟩
  rw [coeffReduction_int]
  exact_mod_cast ZMod.natCast_zmod_val y

theorem coeffReduction_ker (p : ℕ) :
    RingHom.ker (coeffReduction p) =
      Ideal.span ({(2 : Source)^p} : Set Source) := by
  ext z
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hz
    obtain ⟨n,u,rfl⟩ := IsLocalization.mk'_surjective odds z
    have hn : (n : Base p) = 0 := by
      rw [← coeffReduction_fraction p n u, hz, zero_mul]
    obtain ⟨k,hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd n (2^p)).mp hn
    refine ⟨IsLocalization.mk' Source k u, ?_⟩
    have hu : ((2 : Source)^p) = algebraMap ℤ Source ((2^p : ℕ) : ℤ) := by
      simp
    rw [hu, IsLocalization.mul_mk'_eq_mk'_of_mul, ← hk]
  · rintro ⟨y, rfl⟩
    rw [map_mul, map_pow, map_ofNat, base_nilpotent, zero_mul]

/-- The base quotient is precisely the printed mod-2^p coefficient ring. -/
noncomputable def baseQuotient (p : ℕ) :
    (Source ⧸ Ideal.span ({(2 : Source)^p} : Set Source)) ≃+* Base p :=
  (Ideal.quotEquivOfEq (coeffReduction_ker p).symm).trans
    (RingHom.quotientKerEquivOfSurjective (coeffReduction_surjective p))

theorem baseQuotient_mk (p : ℕ) (x : Source) :
    baseQuotient p (Ideal.Quotient.mk _ x) = coeffReduction p x := by
  rw [baseQuotient, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

abbrev IntegralScalar (f : ℤ[X]) := AdjoinRoot (f.map (algebraMap ℤ Source))

/-- The finite scalar ring is isomorphic to the original localized
extension reduced modulo the requested power, not merely a model with
the same residue field. -/
noncomputable def printedScalar (p : ℕ) (f : ℤ[X]) :
    (IntegralScalar f ⧸ Ideal.span ({(2 : IntegralScalar f)^p} : Set (IntegralScalar f))) ≃+*
      Scalar p f := by
  let I := Ideal.span ({(2:Source)^p} : Set Source)
  let F := f.map (algebraMap ℤ Source)
  have hIdeal : Ideal.map (AdjoinRoot.of F) I =
      Ideal.span ({(2 : IntegralScalar f)^p} : Set (IntegralScalar f)) := by
    dsimp only [I]
    rw [Ideal.map_span, Set.image_singleton, map_pow, map_ofNat]
  let E := Polynomial.mapEquiv (baseQuotient p)
  have hMap : E (F.map (Ideal.Quotient.mk I)) = liftPoly p f := by
    change ((F.map (Ideal.Quotient.mk I)).map (baseQuotient p).toRingHom) = liftPoly p f
    dsimp only [F]
    rw [Polynomial.map_map, Polynomial.map_map, liftPoly]
    congr 1
    ext x
    exact (baseQuotient_mk p (algebraMap ℤ Source x)).trans (coeffReduction_int p x)
  have hEq : Ideal.span ({liftPoly p f} : Set (Base p)[X]) =
      Ideal.map E.toRingHom (Ideal.span ({F.map (Ideal.Quotient.mk I)} : Set (Source ⧸ I)[X])) := by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {liftPoly p f} = Ideal.span {E (F.map (Ideal.Quotient.mk I))}
    rw [hMap]
  exact (Ideal.quotEquivOfEq hIdeal.symm).trans
    (((AdjoinRoot.quotEquivQuotMap F I).toRingEquiv).trans
      (Ideal.quotientEquiv _ _ E hEq))

theorem printedScalar_mk (p : ℕ) (f : ℤ[X]) (g : Source[X]) :
    printedScalar p f (Ideal.Quotient.mk _
      (AdjoinRoot.mk (f.map (algebraMap ℤ Source)) g)) =
      AdjoinRoot.mk (liftPoly p f) (g.map (coeffReduction p)) := by
  simp only [printedScalar, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv,
    AdjoinRoot.quotEquivQuotMap_apply_mk]
  apply congrArg (AdjoinRoot.mk (liftPoly p f))
  change ((g.map (Ideal.Quotient.mk _)).map (baseQuotient p).toRingHom) = _
  rw [Polynomial.map_map]
  congr 1

#print axioms printedScalar_mk
#print axioms printedScalar
#print axioms coeffReduction_ker
#print axioms coeffReduction_surjective
#print axioms baseQuotient
#print axioms odd_unit
#print axioms coeffReduction_int
#print axioms coeffReduction_fraction
#print axioms decode_source

end DyadicProbeCompiler