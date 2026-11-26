import P5HermiteTransportGenericShift
import P5HermiteTransportGenericWeights

/-! Expand the SAME D_t L_t E_t compression as a finite sum of
G_tj tensor coefficient slots, also for arbitrary replacement data. -/
namespace Paper5.HermiteGeneric
open Polynomial Matrix
open scoped BigOperators Polynomial Kronecker Classical

variable {K T U V : Type*} [Field K] [Fintype T] [DecidableEq T]

noncomputable def transfer (L : Layout K T) (b : ℕ) (t : T) (j : Fin (L.order t)) :
    Matrix (Fin b) (Fin b) K :=
  decodeMatrix L b t * shiftMatrix K (L.order t) j.val * inputMatrix L b t

theorem transfer_is_shift_power (L : Layout K T) (b : ℕ) (t : T) (j : Fin (L.order t)) :
    transfer L b t j =
      decodeMatrix L b t * (shiftMatrix K (L.order t) 1)^j.val * inputMatrix L b t := by
  rw [shift_power]
  rfl

noncomputable def observedCoefficients (A : Matrix U V K[X]) (t α : K) (k : ℕ) :
    Fin k→Matrix U V K := fun j=>Matrix.of (fun u v=>scalarObserve t α k (A u v) j)

omit [DecidableEq T] [Fintype T] in
noncomputable def nativeCoefficients (L : Layout K T) (A : Matrix U V K[X]) :
    (t : T)→Fin (L.order t)→Matrix U V K :=
  fun t=>observedCoefficients A (L.center t) (L.scale t) (L.order t)

omit [DecidableEq T] [Fintype T] in
noncomputable def anchorMatrix (L : Layout K T) (b : ℕ) (A : Matrix U V K[X]) :
    Matrix (Fin b × U) (Fin b × V) K :=
  convolution (observedCoefficients A L.anchor L.anchorScale b)

noncomputable def expanded (L : Layout K T) (b : ℕ)
    (C : (t : T)→Fin (L.order t)→Matrix U V K) : Matrix (Fin b × U) (Fin b × V) K :=
  ∑ t,∑ j : Fin (L.order t),transfer L b t j ⊗ₖ C t j

variable [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

noncomputable def compressed (L : Layout K T) (b : ℕ)
    (C : (t : T)→Fin (L.order t)→Matrix U V K) : Matrix (Fin b × U) (Fin b × V) K :=
  ∑ t,(decodeMatrix L b t ⊗ₖ (1:Matrix U U K)) * convolution (C t) *
    (inputMatrix L b t ⊗ₖ (1:Matrix V V K))

theorem compression_terms (L : Layout K T) (b : ℕ) (t : T)
    (C : Fin (L.order t)→Matrix U V K) :
    (decodeMatrix L b t ⊗ₖ (1:Matrix U U K)) * convolution C *
      (inputMatrix L b t ⊗ₖ (1:Matrix V V K)) =
      ∑ j,transfer L b t j ⊗ₖ C j := by
  rw [convolution,Matrix.mul_sum,Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [←Matrix.mul_kronecker_mul,←Matrix.mul_kronecker_mul,Matrix.one_mul,Matrix.mul_one]; rfl

theorem compressed_eq_expanded (L : Layout K T) (b : ℕ)
    (C : (t : T)→Fin (L.order t)→Matrix U V K) :
    compressed L b C = expanded L b C := by
  unfold compressed expanded
  exact Finset.sum_congr rfl (fun t _=>compression_terms L b t (C t))

#print axioms transfer_is_shift_power
#print axioms compression_terms
#print axioms compressed_eq_expanded
end Paper5.HermiteGeneric
