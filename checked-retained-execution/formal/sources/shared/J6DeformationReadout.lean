import J6DeformationOrigin

namespace J6DeformationReadout
open scoped Classical BigOperators Polynomial
open Polynomial J6DeformationPoly J6DeformationOrigin

variable {R P K : Type*} [CommRing R] [Algebra ℚ R] [Fintype P] [DecidableEq K]

theorem exact_origin (page : P → K) (slot : P → ℤ) (a : ℕ)
    (A B : (P → Bool) → R)
    (hinj : Function.Injective (fun i => (page i,slot i))) :
    (network page slot a A B).eval 0 = ∑ y, A y * B y := by
  classical
  unfold network
  simp only [eval_finset_sum,eval_mul,eval_C,eval_prod]
  refine Finset.sum_congr rfl (fun Y _ => ?_)
  have hz (x : P → Bool) (i : P) :
      (∑ j, if x j then matrix (R:=R) page slot a i j else 0).eval 0 =
        if x i then 1 else 0 := by
    rw [eval_finset_sum, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · cases e : x i <;> simp [matrix_origin page slot a hinj i i]
    · intro j _ hj
      cases e : x j <;> simp [matrix_origin page slot a hinj i j,Ne.symm hj]
  have hentry (x : P → Bool) (i : P) :
      (if Y i then ∑ j, if x j then matrix (R:=R) page slot a i j else 0
                else 1 - ∑ j, if x j then matrix page slot a i j else 0).eval 0 =
        if x i = Y i then 1 else 0 := by
    cases hy : Y i <;> cases hx : x i <;> simp [hx,eval_sub, hz x i]
  simp only [hentry]
  rw [Finset.sum_eq_single_of_mem Y (Finset.mem_univ Y)]
  · simp
  · intro x _ hx
    obtain ⟨i,hi⟩ : ∃ i, x i ≠ Y i := by
      by_contra! h
      exact hx (funext h)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi), mul_zero]

#print axioms exact_origin
end J6DeformationReadout
