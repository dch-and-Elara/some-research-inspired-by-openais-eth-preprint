import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fintype.BigOperators

/-! Common-observation transfer. The source, input, and observation dimensions
may differ at every node. All output terms must live on the same observation. -/
namespace RankBudget
open scoped BigOperators

variable {F R C A B : Type*} [Field F] [Fintype C]

/-- Rectangular compression and fixed linear regrouping do not increase rank. -/
theorem linearRead_le [Fintype A] [Fintype B] (L : Matrix R A F) (J : Matrix A B F)
    (H : Matrix B C F) : (L * J * H).rank ≤ J.rank :=
  (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- Rank subadditivity, via the ranges of the corresponding linear maps. -/
theorem commonRank_add (A B : Matrix R C F) : (A + B).rank ≤ A.rank + B.rank := by
  change Module.finrank F (LinearMap.range (A + B).mulVecLin) ≤
    Module.finrank F (LinearMap.range A.mulVecLin) + Module.finrank F (LinearMap.range B.mulVecLin)
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le A.mulVecLin B.mulVecLin)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

theorem commonRank_sum {T : Type*} (s : Finset T) (M : T → Matrix R C F) :
    (∑ t ∈ s, M t).rank ≤ ∑ t ∈ s, (M t).rank := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    exact (commonRank_add _ _).trans (Nat.add_le_add_left ih _)

/-- Additive capacity of all source mechanisms after their (signed) linear
read-outs. Nodes may have distinct shapes and arbitrary input/output mixing. -/
theorem observationBudget {T : Type*} (s : Finset T)
    {U V : T → Type*} [∀ t, Fintype (U t)] [∀ t, Fintype (V t)]
    (L : ∀ t, Matrix R (U t) F) (J : ∀ t, Matrix (U t) (V t) F)
    (H : ∀ t, Matrix (V t) C F) (M : Matrix R C F)
    (hs : M = ∑ t ∈ s, L t * J t * H t) :
    M.rank ≤ ∑ t ∈ s, (J t).rank := by
  rw [hs]
  exact (commonRank_sum _ _).trans (Finset.sum_le_sum fun t _ => linearRead_le _ _ _)

/-- Weighted charge into unique operations. The caller must supply
non-duplication / bounded charging, not just an expression with many terms. -/
theorem executionCharge {T G : Type*} (s : Finset T) (gates : Finset G)
    (capacity : T → ℕ) (charge : T → G → ℕ) (cost : G → ℕ) (target : ℕ)
    (hout : target ≤ ∑ t ∈ s, capacity t)
    (hpay : ∀ t ∈ s, capacity t ≤ ∑ g ∈ gates, charge t g)
    (honce : ∀ g ∈ gates, (∑ t ∈ s, charge t g) ≤ cost g) :
    target ≤ ∑ g ∈ gates, cost g := by
  refine hout.trans ((Finset.sum_le_sum hpay).trans ?_)
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum honce

end RankBudget