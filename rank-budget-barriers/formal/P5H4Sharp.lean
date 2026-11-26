import RBLocalProfile

/-! Faithful H4 sharpness: the prescribed polynomial is constructed, and the
profile is computed from actual multiplication in the sampled jet quotients. -/
namespace P5H4
open Polynomial Matrix
open scoped BigOperators Classical

variable {K : Type*} [Field K]

theorem rootMultiplicity_prod {I : Type*} (s : Finset I) (f : I → K[X])
    (hf : ∀ i ∈ s, f i ≠ 0) (t : K) :
    rootMultiplicity t (∏ i ∈ s, f i) = ∑ i ∈ s, rootMultiplicity t (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have h₁ := hf i (Finset.mem_insert_self i s)
    have h₂ : ∀ j ∈ s, f j ≠ 0 := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.prod_insert hi, rootMultiplicity_mul (mul_ne_zero h₁ (Finset.prod_ne_zero_iff.mpr h₂)),
      Finset.sum_insert hi, ih h₂]

/-- The monic polynomial having exactly the specified distinct sampled roots. -/
noncomputable def allocated (s : Finset K) (e : K → ℕ) : K[X] :=
  ∏ t ∈ s, (X - C t) ^ e t

theorem allocated_monic (s : Finset K) (e : K → ℕ) : (allocated s e).Monic := by
  exact monic_prod_of_monic _ _ (fun t _ => (monic_X_sub_C t).pow (e t))

theorem allocated_degree (s : Finset K) (e : K → ℕ) :
    (allocated s e).natDegree = ∑ t ∈ s, e t := by
  unfold allocated
  rw [natDegree_prod_of_monic s _ (fun t _ => (monic_X_sub_C t).pow (e t))]
  refine Finset.sum_congr rfl fun t _ => ?_
  simp [natDegree_pow]

theorem allocated_order (s : Finset K) (e : K → ℕ) (t : K) :
    rootMultiplicity t (allocated s e) = if t ∈ s then e t else 0 := by
  classical
  unfold allocated
  rw [rootMultiplicity_prod _ _ (fun u _ => pow_ne_zero _ (X_sub_C_ne_zero u))]
  have h (u) : rootMultiplicity t ((X - C u) ^ e u) = if u = t then e t else 0 := by
    by_cases hu : u = t
    · subst u
      simp [rootMultiplicity_X_sub_C_pow]
    · rw [if_neg hu]
      apply rootMultiplicity_eq_zero
      unfold IsRoot
      rw [eval_pow, eval_sub, eval_X, eval_C]
      exact pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hu))
  simp_rw [h]
  simp

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Different diagonals can choose unrelated local orders; the assertion
extends to outside nodes, which have order zero, and to truncation k=0. -/
theorem prescribed_diagonal (s : Finset K) (e : n → K → ℕ) (t : K) (k : ℕ) :
    let A := diagonal (fun i => allocated s (e i))
    A.det ≠ 0 ∧
    A.det.natDegree = (∑ i, ∑ u ∈ s, e i u) ∧
    RankBudget.jetLength A t k =
      ∑ i, (k - min k (if t ∈ s then e i t else 0)) := by
  dsimp only
  have hn (i : n) : allocated s (e i) ≠ 0 := (allocated_monic s (e i)).ne_zero
  refine ⟨?_, ?_, ?_⟩
  · rw [det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hn i)
  · rw [det_diagonal, natDegree_prod _ _ (fun i _ => hn i)]
    simp only [allocated_degree]
  · rw [RankBudget.jetLength_diagonal _ hn]
    simp only [allocated_order]

omit [Fintype n] in
/-- The exact entry grade is the largest assigned sum of orders, not the
determinant sum across all diagonal coordinates. This also handles n empty. -/
theorem prescribed_grade (s : Finset K) (e : n → K → ℕ) (d : ℕ) :
    (∀ i j, ((diagonal (fun i => allocated s (e i))) i j).natDegree ≤ d) ↔
      ∀ i, (∑ u ∈ s, e i u) ≤ d := by
  constructor
  · intro h i
    simpa only [diagonal_apply_eq, allocated_degree] using h i i
  · intro h i j
    by_cases hij : i = j
    · subst j
      simpa only [diagonal_apply_eq, allocated_degree] using h i
    · simp [diagonal_apply_ne _ hij]

/-- A constant-times-identity family makes every unit of the scalar
multiplicity budget visible once and only once. The profile is nonuniform. -/
theorem sharp_scalar_identity (s roots : Finset K) (hs : roots ⊆ s) (k : K → ℕ) :
    let A : Matrix n n K[X] := diagonal (fun _ => allocated roots k)
    let d := ∑ u ∈ roots, k u
    (∀ i j, (A i j).natDegree ≤ d) ∧ A.det.natDegree = Fintype.card n * d ∧
    (∑ t ∈ s, (Fintype.card n * k t - RankBudget.jetLength A t (k t))) =
       Fintype.card n * d := by
  dsimp only
  refine ⟨(prescribed_grade roots (fun _ => k) _).2 (fun _ => le_rfl), ?_, ?_⟩
  · rw [(prescribed_diagonal (n:=n) roots (fun _ => k) (0:K) 0).2.1]
    simp
  · have hj (t : K) := (prescribed_diagonal (n:=n) roots (fun _ => k) t (k t)).2.2
    calc
      _ = ∑ t ∈ s, (if t ∈ roots then Fintype.card n * k t else 0) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [hj]
        by_cases ht : t ∈ roots <;> simp [ht]
      _ = ∑ t ∈ roots, Fintype.card n * k t := by
        rw [← Finset.sum_subset hs (f := fun t => if t ∈ roots then Fintype.card n * k t else 0)]
        · exact Finset.sum_congr rfl fun t ht => if_pos ht
        · intro t _ ht
          exact if_neg ht
      _ = _ := (Finset.mul_sum ..).symm

#print axioms rootMultiplicity_prod
#print axioms allocated_order
#print axioms prescribed_diagonal
#print axioms prescribed_grade
#print axioms sharp_scalar_identity
end P5H4
