import J6ActiveTargetSum
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Reindex row choices by the actual target blocks. Source moments can
 be inserted in the product after the row choices are collected. -/
namespace J6BlockFactor
open scoped BigOperators Classical
open J6ActiveAllocation J6ActiveProfile J6ActiveTargetSum
variable {R I M K : Type*} [CommRing R] [Fintype I] [Fintype M] [Fintype K]

def rows (block : I → K) (k : K) := {i : I // block i = k}

def modes (target : M → K) (k : K) := {m : M // target m = k}

def rowEquiv (block : I → K) : (Σ k, rows block k) ≃ I :=
  Equiv.sigmaFiberEquiv block

def allocationEquiv (block : I → K) :
    (I → Option M) ≃ (∀ k, rows block k → Option M) where
  toFun f k i := f i.val
  invFun f i := f (block i) ⟨i, rfl⟩
  left_inv _ := rfl
  right_inv f := by
    funext k i
    rcases i with ⟨i, hi⟩
    subst k
    rfl

noncomputable instance (block : I → K) (k : K) : Fintype (rows block k) := by
  classical
  unfold rows
  infer_instance

noncomputable instance (target : M → K) (k : K) : Fintype (modes target k) := by
  classical
  unfold modes
  infer_instance

omit [CommRing R] [Fintype I] [Fintype M] [Fintype K] in
theorem legal_iff_local (block : I → K) (target : M → K) (x : I → Option M) :
    Legal block target x ↔
      ∀ k (i : rows block k) m, x i.val = some m → k = target m := by
  constructor
  · intro h k i m hm
    exact i.property.symm.trans (h i.val m hm)
  · intro h i m hm
    exact h (block i) ⟨i, rfl⟩ m hm

omit [Fintype M] in
theorem prod_rows (block : I → K) (f : I → R) :
    (∏ i, f i) = ∏ k, ∏ i : rows block k, f i.val := by
  calc
    (∏ i, f i) = ∏ z : Σ k, rows block k, f z.2.val :=
      (Fintype.prod_equiv (rowEquiv block) _ _ (fun _ => rfl)).symm
    _ = _ := Fintype.prod_sigma (fun z : Σ k, rows block k => f z.2.val)

omit [Fintype M] in
theorem sum_with_block_test (block : I → K)
    (ok : ∀ k, (rows block k → Option M) → Prop)
    (f : I → Option M → R) (moment : ∀ k, (rows block k → Option M) → R)
    [Fintype M] :
    (∑ x : I → Option M, if ∀ k, ok k (allocationEquiv block x k) then
        (∏ k, moment k (allocationEquiv block x k)) * (∏ i, f i (x i)) else 0) =
      ∏ k, ∑ y : rows block k → Option M,
        if ok k y then moment k y * (∏ i : rows block k, f i.val (y i)) else 0 := by
  classical
  rw [Fintype.prod_sum]
  refine Fintype.sum_equiv (allocationEquiv block) _ _ ?_
  intro x
  by_cases h : ∀ k, ok k (allocationEquiv block x k)
  · simp only [if_pos h, if_pos (h _)]
    rw [Finset.prod_mul_distrib, prod_rows block (fun i => f i (x i))]
    rfl
  · simp only [if_neg h]
    push_neg at h
    obtain ⟨k, hk⟩ := h
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

#print axioms legal_iff_local
#print axioms prod_rows
#print axioms sum_with_block_test
end J6BlockFactor
