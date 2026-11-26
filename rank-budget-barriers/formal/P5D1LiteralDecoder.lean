import P5D1LiteralLift
import J6ActiveInterpolation
import J6ActiveNormalizer
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! The finite linear map used above is literally the source inverse
Vandermonde followed by the fixed reciprocal and the monic jet remainder. -/
namespace Paper5.D1Literal
open scoped BigOperators
open Polynomial

variable {R : Type*} [CommRing R]

noncomputable def polynomialOfVector (d : ℕ) : (Fin (d+1) → R) →ₗ[R] R[X] where
  toFun b := ∑ j, monomial j.val (b j)
  map_add' b c := by simp only [Pi.add_apply, monomial_add, Finset.sum_add_distrib]
  map_smul' r b := by
    simp only [RingHom.id_apply, Pi.smul_apply, ← smul_monomial, Finset.smul_sum]

noncomputable def interpolateLinear {d : ℕ} (nodes : Fin (d+1) → R) :
    (Fin (d+1) → R) →ₗ[R] R[X] :=
  (polynomialOfVector d).comp ((Matrix.vandermonde nodes)⁻¹).mulVecLin

theorem interpolateLinear_apply {d : ℕ} (nodes b : Fin (d+1) → R) :
    interpolateLinear nodes b = J6ActiveInterpolation.decoded nodes b := rfl

noncomputable def multiplyBy (p : R[X]) : R[X] →ₗ[R] R[X] where
  toFun q := q*p
  map_add' _ _ := add_mul _ _ _
  map_smul' _ _ := smul_mul_assoc _ _ _

noncomputable def quotientLinear (k : ℕ) (normal : R[X]) : R[X] →ₗ[R] R[X] :=
  (Polynomial.modByMonicHom (X^k)).comp (multiplyBy (∑ j ∈ Finset.range k, (1-normal)^j))

theorem quotientLinear_apply (k : ℕ) (normal p : R[X]) :
    quotientLinear k normal p = J6ActiveNormalizer.quotientJet k normal p := rfl

noncomputable def nativeDecoder {d : ℕ} (nodes : Fin (d+1) → R) (k : ℕ)
    (normal : R[X]) : (Fin (d+1) → R) →ₗ[R] (ℕ → R) :=
  (LinearMap.pi fun j => Polynomial.lcoeff R j).comp
    ((quotientLinear k normal).comp (interpolateLinear nodes))

theorem nativeDecoder_apply {d : ℕ} (nodes b : Fin (d+1) → R) (k j : ℕ) (normal : R[X]) :
    nativeDecoder nodes k normal b j =
      (J6ActiveNormalizer.quotientJet k normal (J6ActiveInterpolation.decoded nodes b)).coeff j := rfl

theorem native_decoder_lift_reduces {A M G : Type*} [CommRing A] [Fintype M] [Fintype G]
    {d : ℕ} (nodes : Fin (d+1) → R) (k j : ℕ) (normal : R[X])
    (reduce : A →+* R) (lift : R → A) (hlift : ∀ x, reduce (lift x) = x)
    (child : Fin (d+1) → M → G → R) :
    reduce (liftedCoefficient (nativeDecoder nodes k normal) lift
      (fun z => liftedChildSum lift (child z)) j) =
      (J6ActiveNormalizer.quotientJet k normal
        (J6ActiveInterpolation.decoded nodes (fun z => ∑ m, ∏ g, child z m g))).coeff j := by
  rw [reduce_liftedChild_decode _ reduce lift hlift, nativeDecoder_apply]

#print axioms interpolateLinear_apply
#print axioms quotientLinear_apply
#print axioms nativeDecoder_apply
#print axioms native_decoder_lift_reduces
end Paper5.D1Literal

