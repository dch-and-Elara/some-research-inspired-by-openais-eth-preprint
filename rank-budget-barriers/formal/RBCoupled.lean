import RBObservation
import RBJets

namespace RankBudget
open Polynomial Matrix Module
open scoped BigOperators

variable {K n : Type*} [Field K] [Fintype n]

/-- Applying a field-linear functional to each entry of a truncated matrix
cannot exceed the dimension of its full multiplication image. A scalar-valued
functional is used once, not k independently charged evaluations. -/
theorem readJet_rank_le (P : Matrix n n K[X]) (t : K) (k : ℕ) (ℓ : Jet t k →ₗ[K] K) :
    (P.map (fun p => ℓ (AdjoinRoot.mk ((X - C t) ^ k) p))).rank ≤ jetLength P t k := by
  classical
  let q : K[X] := (X - C t) ^ k
  letI : Module.Finite K (Jet t k) := ((monic_X_sub_C t).pow k).finite_adjoinRoot
  let lift : (n → K) →ₗ[K] (n → Jet t k) :=
    LinearMap.pi fun j => (Algebra.linearMap K (Jet t k)).comp (LinearMap.proj j)
  let read : (n → Jet t k) →ₗ[K] (n → K) :=
    LinearMap.pi fun i => ℓ.comp (LinearMap.proj i)
  let G := (jetMul P t k).rangeRestrict.comp lift
  let H := read.comp (LinearMap.range (jetMul P t k)).subtype
  have he : (P.map (fun p => ℓ (AdjoinRoot.mk q p))).mulVecLin = H.comp G := by
    ext v i
    change (∑ j, ℓ (AdjoinRoot.mk q (P i j)) * _) =
      ℓ (∑ j, (AdjoinRoot.mk q (P i j)) * _)
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change ℓ (AdjoinRoot.mk q (P i j)) * _ =
      ℓ (AdjoinRoot.mk q (P i j) * algebraMap K (Jet t k) _)
    rw [mul_comm (AdjoinRoot.mk q (P i j)), ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]
    rfl
  change Module.finrank K (LinearMap.range ((P.map (fun p => ℓ (AdjoinRoot.mk q p))).mulVecLin)) ≤ _
  rw [he]
  exact (Submodule.finrank_mono (LinearMap.range_comp_le_range G H)).trans H.finrank_range_le

/-- A single target simultaneously imposes final-output and degree constraints
on the *same* jet lengths at the *same* nodes. E packages any additional
linear observation, in particular a signed sum of other factored mechanisms. -/
theorem coupledJetBudget [DecidableEq n] (P : Matrix n n K[X]) (d : ℕ) (s : Finset K)
    (k : K → ℕ) (ℓ : ∀ t, Jet t (k t) →ₗ[K] K) (hp : P.det ≠ 0)
    (hdeg : ∀ i j, (P i j).natDegree ≤ d) (M E : Matrix n n K)
    (hout : M = (∑ t ∈ s, P.map (fun p => ℓ t (AdjoinRoot.mk ((X - C t) ^ k t) p))) + E) :
    (∑ t ∈ s, (Fintype.card n * k t - jetLength P t (k t))) ≤ Fintype.card n * d ∧
    M.rank ≤ (∑ t ∈ s, jetLength P t (k t)) + E.rank := by
  refine ⟨jetDefectBudget P d s k hp hdeg, ?_⟩
  rw [hout]
  refine (commonRank_add _ _).trans (Nat.add_le_add_right ?_ _)
  exact (commonRank_sum ..).trans (Finset.sum_le_sum fun t _ => readJet_rank_le P t (k t) (ℓ t))

end RankBudget