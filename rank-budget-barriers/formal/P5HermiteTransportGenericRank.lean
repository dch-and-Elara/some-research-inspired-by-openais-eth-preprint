import P5HermiteTransportGenericExpansion
import SeparatedRank
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The two actual rank budgets for arbitrary replacement matrices.
A tensor rank bound uses an exact factorization through the rank
spaces, not a proxy or an assumed coefficient-factor receipt. -/
namespace Paper5.HermiteGeneric
open Matrix Module
open scoped BigOperators Kronecker Classical

variable {K U V Y Z : Type*} [Field K]
  [Fintype U] [Fintype V] [DecidableEq V]

set_option maxHeartbeats 9500000 in
omit [Fintype U] in
theorem rank_factorization (A : Matrix U V K) :
    ∃ B : Matrix U (Fin A.rank) K,∃ C : Matrix (Fin A.rank) V K,B*C=A := by
  let N := LinearMap.range A.mulVecLin
  let basis : Basis (Fin A.rank) K N := Module.finBasis K N
  have hh (j : V) : (fun i=>A i j)∈N := by
    refine ⟨Pi.single j 1,?_⟩
    change A *ᵥ Pi.single j 1=_
    funext i
    simp [Matrix.mulVec_single]
  let cj (j : V) : N := ⟨fun i=>A i j,hh j⟩
  let B : Matrix U (Fin A.rank) K := Matrix.of fun i r=>(basis r).val i
  let C : Matrix (Fin A.rank) V K := Matrix.of fun r j=>basis.repr (cj j) r
  refine ⟨B,C,?_⟩
  ext i j
  have h := congrArg (fun a : N=>a.val i) (basis.sum_repr (cj j))
  change (∑ r : Fin A.rank,(basis r).val i*basis.repr (cj j) r)=A i j
  simpa only [Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,Pi.smul_apply,
    smul_eq_mul,mul_comm,cj] using h

variable [Fintype Y] [Fintype Z] [DecidableEq Z]

omit [Fintype U] [Fintype Y] in
theorem kronecker_rank_le (A : Matrix U V K) (B : Matrix Y Z K) :
    (A ⊗ₖ B).rank ≤ A.rank*B.rank := by
  obtain ⟨L,R,hA⟩ := rank_factorization A
  obtain ⟨S,T,hB⟩ := rank_factorization B
  suffices (L ⊗ₖ S * (R ⊗ₖ T)).rank ≤ A.rank*B.rank by
    rwa [←Matrix.mul_kronecker_mul,hA,hB] at this
  have h := (Matrix.rank_mul_le_left (L ⊗ₖ S) (R ⊗ₖ T)).trans
    (Matrix.rank_le_card_width (L ⊗ₖ S))
  simpa only [Fintype.card_prod,Fintype.card_fin] using h

variable {T : Type*} [Fintype T] [DecidableEq T] [DecidableEq U]

theorem compressed_rank_bound (L : Layout K T) (b : ℕ)
    (C : (t : T)→Fin (L.order t)→Matrix U V K) :
    (compressed L b C).rank ≤ ∑ t,(convolution (C t)).rank := by
  unfold compressed
  refine (SeparatedRank.rank_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro t _
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

omit [DecidableEq U] in
theorem expanded_rank_bound (L : Layout K T) (b : ℕ)
    (C : (t : T)→Fin (L.order t)→Matrix U V K) :
    (expanded L b C).rank ≤ ∑t,∑j,(transfer L b t j).rank*(C t j).rank := by
  unfold expanded
  refine (SeparatedRank.rank_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro t _
  refine (SeparatedRank.rank_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro j _
  exact kronecker_rank_le (transfer L b t j) (C t j)

#print axioms rank_factorization
#print axioms kronecker_rank_le
#print axioms compressed_rank_bound
#print axioms expanded_rank_bound
end Paper5.HermiteGeneric
