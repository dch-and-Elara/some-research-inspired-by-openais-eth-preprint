import RBDeterminant
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Polynomial.Basic

/-! Exact local-image budgets at nonuniform nodes. The quotient and its
multiplication map are actual algebraic objects, not numeric certificates. -/
namespace RankBudget
open Polynomial Matrix Module
open scoped BigOperators

variable {K n : Type*} [Field K] [Fintype n]

/-- Quotient corresponding to Hasse-jet precision k at t, including k=0. -/
abbrev Jet (t : K) (k : ℕ) := AdjoinRoot ((X - C t) ^ k)

/-- Multiplication by the reduced polynomial matrix, viewed over the base field. -/
noncomputable def jetMul (P : Matrix n n K[X]) (t : K) (k : ℕ) :
    (n → Jet t k) →ₗ[K] (n → Jet t k) :=
  ((P.map (AdjoinRoot.mk ((X - C t) ^ k))).mulVecLin).restrictScalars K

noncomputable def jetLength (P : Matrix n n K[X]) (t : K) (k : ℕ) : ℕ :=
  Module.finrank K (LinearMap.range (jetMul P t k))

theorem jetLength_le (P : Matrix n n K[X]) (t : K) (k : ℕ) :
    jetLength P t k ≤ Fintype.card n * k := by
  letI : Module.Finite K (Jet t k) := ((monic_X_sub_C t).pow k).finite_adjoinRoot
  have hd : Module.finrank K (Jet t k) = k := by
    rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasisAux' ((monic_X_sub_C t).pow k))]
    simp
  exact (jetMul P t k).finrank_range_le.trans_eq (by rw [Module.finrank_pi_fintype]; simp [hd])

/-- Reduce a bounded vector modulo the node polynomial. -/
noncomputable def reduceBounded (m : ℕ) (t : K) (k : ℕ) :
    (n → degreeLT K m) →ₗ[K] (n → Jet t k) :=
  LinearMap.pi fun i => (AdjoinRoot.mkₐ ((X - C t) ^ k)).toLinearMap.comp
    ((degreeLT K m).subtype.comp (LinearMap.proj i))

private theorem mulVec_degree_bound (P : Matrix n n K[X]) (d m : ℕ) (hm : 0 < m)
    (hdeg : ∀ i j, (P i j).natDegree ≤ d) (v : n → degreeLT K m) (i : n) :
    ((P *ᵥ fun j => (v j : K[X])) i).natDegree ≤ d + (m-1) := by
  change (∑ j, P i j * (v j : K[X])).natDegree ≤ _
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  apply (Polynomial.natDegree_mul_le ..).trans
  apply Nat.add_le_add (hdeg i j)
  by_cases hv : (v j : K[X]) = 0
  · simp [hv]
  · have hj := (natDegree_lt_iff_degree_lt hv).mpr (mem_degreeLT.mp (v j).property)
    omega

/-- The global jet map on all inputs of degree < sum(k)-d is injective.
We keep its output in the product of the actual multiplication images. -/
theorem jetImageDimension [DecidableEq n] (P : Matrix n n K[X]) (d : ℕ) (s : Finset K)
    (k : K → ℕ) (hp : P.det ≠ 0) (hdeg : ∀ i j, (P i j).natDegree ≤ d) :
    Fintype.card n * ((∑ t ∈ s, k t) - d) ≤ ∑ t ∈ s, jetLength P t (k t) := by
  classical
  let m := (∑ t ∈ s, k t) - d
  by_cases hpos : 0 < m
  · letI (t : ↥s) : Module.Finite K (Jet t.1 (k t)) :=
      ((monic_X_sub_C t.1).pow (k t)).finite_adjoinRoot
    let G : (n → degreeLT K m) →ₗ[K] ((t : ↥s) → LinearMap.range (jetMul P t.1 (k t))) :=
      LinearMap.pi fun t => (jetMul P t.1 (k t)).rangeRestrict.comp (reduceBounded m t.1 (k t))
    have injective : Function.Injective G := by
      apply LinearMap.ker_eq_bot.mp
      apply LinearMap.ker_eq_bot'.mpr
      intro v hv
      let w : n → K[X] := fun j => v j
      have hrow (i : n) : (P *ᵥ w) i = 0 := by
        by_contra hn
        have hz : ∀ t ∈ s, (X - C t) ^ k t ∣ (P *ᵥ w) i := by
          intro t ht
          apply AdjoinRoot.mk_eq_zero.mp
          rw [RingHom.map_mulVec]
          exact congrArg (fun f => (f ⟨t,ht⟩).val i) hv
        have hlow := multiplicityBudget _ hn s k hz
        have hhigh := mulVec_degree_bound P d m hpos hdeg v i
        change ((P *ᵥ w) i).natDegree ≤ d + (m-1) at hhigh
        dsimp [m] at *
        omega
      have hw : w = 0 := by
        by_contra hw
        exact hp ((Matrix.exists_mulVec_eq_zero_iff).mp ⟨_, hw, funext hrow⟩)
      funext i
      exact Subtype.ext (congrFun hw i)
    have hdim := LinearMap.finrank_le_finrank_of_injective injective
    letI : Module.Finite K (degreeLT K m) := Module.Finite.equiv (degreeLTEquiv K m).symm
    have hsmall : Module.finrank K (degreeLT K m) = m := by
      rw [(degreeLTEquiv K m).finrank_eq, Module.finrank_pi, Fintype.card_fin]
    rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype] at hdim
    rw [← Finset.sum_coe_sort s (fun t => jetLength P t (k t))]
    simp only [hsmall, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hdim
    exact hdim
  · have hm : (∑ t ∈ s, k t) - d = 0 := by omega
    simp [hm]

/-- Exact length-defect budget with genuine module images, including distinct
nodes of nonuniform precision, in arbitrary characteristic. -/
theorem jetDefectBudget [DecidableEq n] (P : Matrix n n K[X]) (d : ℕ) (s : Finset K)
    (k : K → ℕ) (hp : P.det ≠ 0) (hdeg : ∀ i j, (P i j).natDegree ≤ d) :
    (∑ t ∈ s, (Fintype.card n * k t - jetLength P t (k t))) ≤ Fintype.card n * d := by
  have hi := jetImageDimension P d s k hp hdeg
  rw [Nat.mul_sub, Nat.sub_le_iff_le_add] at hi
  have he : (∑ t ∈ s, (Fintype.card n * k t - jetLength P t (k t))) +
      (∑ t ∈ s, jetLength P t (k t)) = Fintype.card n * ∑ t ∈ s, k t := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => Nat.sub_add_cancel (jetLength_le P t (k t))
  omega

end RankBudget