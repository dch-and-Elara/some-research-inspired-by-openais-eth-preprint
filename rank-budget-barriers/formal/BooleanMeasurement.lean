import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Matrix.Rank

/-! Cardinality of a finite Boolean measurement image. -/

set_option autoImplicit false

noncomputable section
open scoped BigOperators

namespace BooleanMeasurement

variable {K J V : Type*} [Field K] [Fintype J] [AddCommGroup V] [Module K V]

/-- The scalar encoded by a Boolean coordinate. -/
def bit (K : Type*) [Zero K] [One K] (b : Bool) : K := if b then 1 else 0

lemma bit_injective : Function.Injective (bit K) := by
  intro b c h
  cases b <;> cases c <;> simp_all [bit]

/-- The measurement with `columns` as its columns and `x` as its Boolean input. -/
def measure (K : Type*) [Field K] [Module K V] (columns : J → V) (x : J → Bool) : V :=
  ∑ j, bit K (x j) • columns j

/-- A subset of the original column indices gives an independent spanning family
whose cardinality is the dimension of the full column span. -/
theorem exists_independent_columns (columns : J → V) :
    ∃ s : Set J, LinearIndepOn K columns s ∧
      Submodule.span K (columns '' s) = Submodule.span K (Set.range columns) ∧
      s.ncard = Module.finrank K (Submodule.span K (Set.range columns)) := by
  classical
  obtain ⟨s, _, _, hgen, hs⟩ := exists_linearIndepOn_extension
    (linearIndepOn_empty K columns) (Set.empty_subset (Set.univ : Set J))
  rw [Set.image_univ] at hgen
  have hspan : Submodule.span K (columns '' s) = Submodule.span K (Set.range columns) :=
    le_antisymm (Submodule.span_mono (Set.image_subset_range ..)) (Submodule.span_le.mpr hgen)
  refine ⟨s, hs, hspan, ?_⟩
  rw [← hspan, Set.image_eq_range]
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact
    (finrank_span_eq_card (show LinearIndependent K (fun j : s => columns j) from hs)).symm

/-- Distinct Boolean inputs to an independent family give distinct measured vectors. -/
theorem measure_injective_of_independent {columns : J → V} (hc : LinearIndependent K columns) :
    Function.Injective (measure K columns) := by
  intro x y h
  funext j
  exact bit_injective <| Fintype.linearIndependent_iffₛ.mp hc _ _ h j

/-- Each measurement on a subset of the columns is attained on the full Boolean cube,
by setting every unselected input to `false`. -/
theorem range_restrict_measure_subset (columns : J → V) (s : Set J) [DecidablePred (· ∈ s)] :
    Set.range (measure K (fun j : s => columns j)) ⊆ Set.range (measure K columns) := by
  classical
  rintro _ ⟨x, rfl⟩
  let y (j : J) := if h : j ∈ s then x ⟨j, h⟩ else false
  refine ⟨y, ?_⟩
  unfold measure
  apply Finset.sum_congr_set s
  · intro j hj
    simp [y, hj]
  · intro j hj
    simp [y, hj, bit]

/-- The Boolean image of a finite family has at least two to the dimension of its span
many members. The codomain may be infinite-dimensional. -/
theorem two_pow_finrank_le_range_ncard (columns : J → V) :
    2 ^ Module.finrank K (Submodule.span K (Set.range columns)) ≤
      (Set.range (measure K columns)).ncard := by
  classical
  obtain ⟨s, hs, _, hcard⟩ := exists_independent_columns (K := K) columns
  have hinj := measure_injective_of_independent
    (show LinearIndependent K (fun j : s => columns j) from hs)
  have hle := Set.ncard_le_ncard (range_restrict_measure_subset (K := K) columns s)
    (Set.finite_range _)
  rw [Set.ncard_range_of_injective hinj] at hle
  rw [← hcard]
  rw [← Nat.card_coe_set_eq s, Nat.card_eq_fintype_card]
  simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool] using hle

variable {I : Type*}

/-- A matrix measured on the Boolean cube using actual matrix-vector multiplication. -/
theorem two_pow_rank_le_mulVec_range_ncard (C : Matrix I J K) :
    2 ^ C.rank ≤ (Set.range (fun x : J → Bool => C.mulVec (fun j => bit K (x j)))).ncard := by
  have heq : (fun x : J → Bool => C.mulVec (fun j => bit K (x j))) = measure K C.col := by
    funext x i
    simp [Matrix.mulVec, dotProduct, measure, Finset.sum_apply, Pi.smul_apply, mul_comm,
      Matrix.col_apply]
  rw [heq, C.rank_eq_finrank_span_cols]
  exact two_pow_finrank_le_range_ncard C.col

/-- The same bound for the literal coordinatewise `{0,1}` subset of rational vectors. -/
theorem two_pow_rank_le_rational_cube_image_ncard (C : Matrix I J ℚ) :
    2 ^ C.rank ≤ (C.mulVec '' {x : J → ℚ | ∀ j, x j = 0 ∨ x j = 1}).ncard := by
  classical
  have hcube : {x : J → ℚ | ∀ j, x j = 0 ∨ x j = 1} =
      Set.range (fun x : J → Bool => fun j => bit ℚ (x j)) := by
    ext x
    constructor
    · intro hx
      refine ⟨fun j => decide (x j = 1), ?_⟩
      funext j
      rcases hx j with h | h <;> simp [h, bit]
    · rintro ⟨x, rfl⟩ j
      cases x j <;> simp [bit]
  rw [hcube, ← Set.range_comp]
  exact two_pow_rank_le_mulVec_range_ncard C

/-- Any node statistic that decodes the global matrix measurement has at least as many
attainable values. This includes tuples decoded by summing the group contributions. -/
theorem two_pow_rank_le_summary_range_ncard {T : Type*} (C : Matrix I J K)
    (summary : (J → Bool) → T) (decode : T → I → K)
    (hdecode : ∀ x, decode (summary x) = C.mulVec (fun j => bit K (x j))) :
    2 ^ C.rank ≤ (Set.range summary).ncard := by
  apply (two_pow_rank_le_mulVec_range_ncard C).trans
  have heq : Set.range (fun x : J → Bool => C.mulVec (fun j => bit K (x j))) =
      decode '' (Set.range summary) := by
    rw [← Set.range_comp]
    exact congrArg Set.range (funext fun x => (hdecode x).symm)
  rw [heq]
  exact Set.ncard_image_le (Set.finite_range _)

/-- The tuple of measurements for the groups of any labeling has at least `2 ^ C.rank`
attainable values. Empty groups and repeated or zero columns are allowed. -/
theorem two_pow_rank_le_grouped_range_ncard {G : Type*} [Fintype G] [DecidableEq G]
    (C : Matrix I J K) (group : J → G) :
    2 ^ C.rank ≤ (Set.range (fun (x : J → Bool) (g : G) =>
      C.mulVec (fun j => if group j = g then bit K (x j) else 0))).ncard := by
  apply two_pow_rank_le_summary_range_ncard C _ (fun y => ∑ g, y g)
  intro x
  funext i
  simp only [Finset.sum_apply, Matrix.mulVec, dotProduct, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  simp

end BooleanMeasurement

#print axioms BooleanMeasurement.bit_injective
#print axioms BooleanMeasurement.exists_independent_columns
#print axioms BooleanMeasurement.measure_injective_of_independent
#print axioms BooleanMeasurement.range_restrict_measure_subset
#print axioms BooleanMeasurement.two_pow_finrank_le_range_ncard
#print axioms BooleanMeasurement.two_pow_rank_le_mulVec_range_ncard
#print axioms BooleanMeasurement.two_pow_rank_le_rational_cube_image_ncard
#print axioms BooleanMeasurement.two_pow_rank_le_summary_range_ncard
#print axioms BooleanMeasurement.two_pow_rank_le_grouped_range_ncard
