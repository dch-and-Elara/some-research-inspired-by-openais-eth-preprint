import Paper1Eq18
import BooleanCube.TailReflection
import BooleanCube.SymmetricDegree

/-! Paper 1: explicit links between the original pair-input model and (1),
the finite Walsh-row realization for every deleted family, the full order
of minima, and the original normalized square consequence (20). -/
namespace LocalReconstruction.Paper1Coverage

open Polynomial
open scoped BigOperators Polynomial
noncomputable section

/-- The literal pair-input requirement: same shared measurements and same
complementary half-cube imply the same reconstructed output. -/
def pairInputCondition {ι : Type*} {q : ℕ} (a : Fin q → ℚ)
    (C : Matrix ι (Cube q) ℚ) (P : Matrix (Cube q) (Cube q) ℚ[X]) : Prop :=
  ∀ (u : Cube q) (i : Fin q) (x y : Cube q → ℚ),
    (∀ j, ∑ v, C j v * x v = ∑ v, C j v * y v) →
    (∀ v, v i ≠ u i → x v = y v) →
    ∑ v, (P u v).eval (a i) * x v = ∑ v, (P u v).eval (a i) * y v

theorem original_pair_input_iff_matrix_condition {ι : Type*} {q d : ℕ}
    (a : Fin q → ℚ) (C : Matrix ι (Cube q) ℚ) (P : Matrix (Cube q) (Cube q) ℚ[X]) :
    matrixCondition a C d P ↔
      (∀ u v, (P u v).natDegree ≤ d) ∧
        (∀ u v, (P u v).eval 0 = if u = v then 1 else 0) ∧ pairInputCondition a C P := by
  constructor
  · rintro ⟨hd,h0,h⟩
    refine ⟨hd,h0,?_⟩
    intro u i x y hsame hcoords
    have hTest : rowTest C (fun v => x v - y v) := by
      intro j
      simpa only [mul_sub, Finset.sum_sub_distrib, sub_eq_zero] using hsame j
    have hHalf : halfSupport i u (fun v => x v - y v) := fun v hv => sub_eq_zero.mpr (hcoords v hv)
    simpa only [mul_sub, Finset.sum_sub_distrib, sub_eq_zero] using h u i _ hTest hHalf
  · rintro ⟨hd,h0,h⟩
    refine ⟨hd,h0,?_⟩
    intro u i x hsame hcoords
    have hz := h u i x (fun _ => 0) (fun j => by simpa using hsame j)
      (fun v hv => hcoords v hv)
    simpa using hz

/-- One actual Walsh row for each member of any finite deleted family. -/
def selectedWalshRows {q : ℕ} (A : Finset (Cube q)) :
    Matrix (↥A) (Cube q) ℚ := fun s => walsh s.val

private theorem selected_walsh_sign {q : ℕ} (s x : Cube q) : walsh s x = -1 ∨ walsh s x = 1 := by
  have H : walsh s x * walsh s x = 1 := by
    unfold walsh
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i _
    cases s i <;> cases x i <;> norm_num [signBit]
  have h : (walsh s x + 1)*(walsh s x-1) = 0 := by nlinarith
  rcases mul_eq_zero.mp h with h | h
  · left
    linarith
  · right
    linarith

theorem selected_walsh_rows_ternary {q : ℕ} (A : Finset (Cube q)) : Ternary (selectedWalshRows A) := by
  intro s x
  rcases selected_walsh_sign s.val x with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

theorem selected_walsh_rows_row_space {q : ℕ} (A : Finset (Cube q)) :
    rowSpace (selectedWalshRows A) = walshSpace (↑A : Set (Cube q)) := by
  change Submodule.span ℚ (Set.range fun s : ↥A => walsh s.val) = _
  rw [walshSpace]
  congr 1
  ext f
  simp

theorem arbitrary_walsh_space_rank {q : ℕ} (A : Finset (Cube q)) :
    Module.finrank ℚ (walshSpace (↑A : Set (Cube q))) = A.card := by
  have lin : LinearIndependent ℚ (fun s : ↥A => walsh s.val) :=
    (walsh_independent q).comp _ Subtype.val_injective
  rw [← selected_walsh_rows_row_space]
  exact (finrank_span_eq_card lin).trans (Fintype.card_coe A)

/-- Lemma 1, with concrete ternary rows for any family, not just layer unions. -/
theorem arbitrary_family_row_realization {q : ℕ} (A : Finset (Cube q)) :
    ∃ C : Matrix (Fin A.card) (Cube q) ℚ, Ternary C ∧
      rowSpace C = walshSpace (↑A : Set (Cube q)) := by
  let e : ↥A ≃ Fin A.card := (Fintype.equivFin ↥A).trans (finCongr (Fintype.card_coe A))
  let C : Matrix (Fin A.card) (Cube q) ℚ := fun i => selectedWalshRows A (e.symm i)
  refine ⟨C,fun i => selected_walsh_rows_ternary A (e.symm i),?_⟩
  rw [← selected_walsh_rows_row_space]
  change Submodule.span ℚ (Set.range (selectedWalshRows A ∘ e.symm)) =
    Submodule.span ℚ (Set.range (selectedWalshRows A))
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨e.symm i, rfl⟩
  · rintro ⟨s, rfl⟩
    exact ⟨e s, by simp⟩

theorem arbitrary_family_budget_characterization {q : ℕ} (W : Submodule ℚ (Cube q → ℚ))
    (b : ℕ) :
    (FlipInvariant W ∧ ∃ m ≤ b, ∃ C : Matrix (Fin m) (Cube q) ℚ, Ternary C ∧ rowSpace C = W) ↔
      ∃ A : Finset (Cube q), A.card ≤ b ∧ W = walshSpace (↑A : Set (Cube q)) := by
  classical
  constructor
  · rintro ⟨hf,m,hm,C,_,hC⟩
    obtain ⟨S,hS⟩ := (flipInvariant_iff W).mp hf
    let A := S.toFinset
    have hh : W = walshSpace (↑A : Set (Cube q)) := by simpa [A] using hS
    refine ⟨A, ?_, hh⟩
    rw [← arbitrary_walsh_space_rank A, ← hh, ← hC]
    exact (finrank_range_le_card C).trans (by simpa using hm)
  · rintro ⟨A,hA,rfl⟩
    obtain ⟨C,ht,hs⟩ := arbitrary_family_row_realization A
    exact ⟨(flipInvariant_iff _).mpr ⟨_,rfl⟩,_,hA,C,ht,hs⟩

theorem rational_unrestricted_degree_le_ternary (q : ℕ) (γ : ℝ) :
    unrestrictedDegree false q γ ≤ unrestrictedDegree true q γ := by
  obtain ⟨m,hm,C,_,P,hp⟩ := unrestrictedDegree_feasible true q γ
  apply Nat.sInf_le (s := {d | unrestrictedScheme false q d γ})
  exact ⟨m,hm,C,(fun h => by cases h),P,hp⟩

theorem original_minima_order (q : ℕ) (γ : ℝ) :
    0 ≤ unrestrictedDegree false q γ ∧
      unrestrictedDegree false q γ ≤ unrestrictedDegree true q γ ∧
      unrestrictedDegree true q γ ≤ asymmetricDegree q γ ∧
      asymmetricDegree q γ ≤ symmetricDegree q γ ∧ symmetricDegree q γ ≤ q :=
  ⟨Nat.zero_le _, rational_unrestricted_degree_le_ternary q γ,
    unrestrictedDegree_le_asymmetric true q γ, asymmetricDegree_le_symmetric q γ,
    symmetricDegree_le_of_scheme (realSymmetricScheme_at_dimension q γ)⟩

/-- The normalized finite square-budget consequence exactly as printed
in (20), with the original floor cutoff. -/
theorem bit_flip_square_normalized_eq20 {q d : ℕ} {γ : ℝ}
    (h : realAsymmetricScheme q d γ) (hd : d < q) :
    let k := (q-d-1)/2
    weightedTail q k / (((k:ℝ)+1)*(2:ℝ)^q) ≤ (q:ℝ)^(-γ) := by
  let k := (q-d-1)/2
  obtain ⟨m, hm, M, _, _, P, hp⟩ := h
  have hb := matrix_square_budget (k := k) (printedLabels_injective q) printedLabels_nonzero hp
    (show d+2*k < q by dsimp [k]; omega)
  have hB : weightedTail q k ≤ ((k:ℝ)+1)*(m:ℝ) := by
    have hr := (Nat.cast_le (α := ℝ)).mpr hb
    unfold weightedTail
    push_cast at hr
    exact hr
  have hpos : 0 < ((k:ℝ)+1)*(2:ℝ)^q := by positivity
  have hq : 0 < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  change weightedTail q k / (((k:ℝ)+1)*(2:ℝ)^q) ≤ (q:ℝ)^(-γ)
  apply (div_le_iff₀ hpos).mpr
  rw [Real.rpow_neg hq.le]
  calc
    weightedTail q k ≤ ((k:ℝ)+1)*measurementBudget q γ :=
      hB.trans (mul_le_mul_of_nonneg_left hm (by positivity))
    _ = _ := by unfold measurementBudget; rw [div_eq_mul_inv]; ring

end
end LocalReconstruction.Paper1Coverage

#print axioms LocalReconstruction.Paper1Coverage.original_pair_input_iff_matrix_condition
#print axioms LocalReconstruction.Paper1Coverage.selected_walsh_rows_ternary
#print axioms LocalReconstruction.Paper1Coverage.selected_walsh_rows_row_space
#print axioms LocalReconstruction.Paper1Coverage.arbitrary_walsh_space_rank
#print axioms LocalReconstruction.Paper1Coverage.arbitrary_family_row_realization
#print axioms LocalReconstruction.Paper1Coverage.arbitrary_family_budget_characterization
#print axioms LocalReconstruction.Paper1Coverage.rational_unrestricted_degree_le_ternary
#print axioms LocalReconstruction.Paper1Coverage.original_minima_order
#print axioms LocalReconstruction.Paper1Coverage.bit_flip_square_normalized_eq20
