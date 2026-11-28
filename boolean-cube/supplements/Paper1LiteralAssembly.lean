import Paper1LiteralBudget
import Paper1LiteralEq9
import Paper1ModelCorrespondence

/-! Independent exact link of the three printed constructions: Walsh rows
on the single actual residue class (11), exact maximal-run polynomials
(9), and the spectral matrix (8). -/

namespace LocalReconstruction.Paper1Coverage

open Polynomial Filter
open scoped BigOperators Polynomial Topology
noncomputable section

/-- The displayed matrix (8), with its actual rational normalization. -/
def literalSpectralMatrix {q : ℕ} (p : Cube q → ℚ[X]) : Matrix (Cube q) (Cube q) ℚ[X] :=
  fun u v => ∑ s : Cube q, Polynomial.C (walsh s u * walsh s v / (2:ℚ)^q) * p s

private theorem flip_coefficient_on_half {q : ℕ} (s : Cube q) {i : Fin q} {u : Cube q}
    {h : Cube q → ℚ} (hh : halfSupport i u h) :
    coefficient (flip i s) h = coefficient s h * signBit true (u i) := by
  unfold coefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [walsh_flip]
  by_cases he : x i = u i
  · rw [he, mul_assoc]
  · simp [hh x he]

private theorem spectral_edge_sum {q d : ℕ} {labels : Fin q → ℚ} {A : Set (Cube q)}
    {p : Cube q → ℚ[X]} (hp : edgeCondition labels A d p) (u : Cube q) (i : Fin q)
    (h : Cube q → ℚ) (hk : ∀ s ∈ A, coefficient s h = 0) (hh : halfSupport i u h) :
    (∑ s : Cube q, (p s).eval (labels i) * walsh s u * coefficient s h) = 0 := by
  classical
  let g := fun s : Cube q => (p s).eval (labels i) * walsh s u * coefficient s h
  have hneg (s : Cube q) : g s + g (flip i s) = 0 := by
    simp only [g, walsh_flip, flip_coefficient_on_half s hh]
    by_cases hs : s ∈ A
    · simp [hk s hs]
    by_cases ht : flip i s ∈ A
    · have z := hk _ ht
      rw [flip_coefficient_on_half s hh] at z
      have he : signBit true (u i) ≠ 0 := by cases hbit : u i <;> norm_num [signBit]
      simp [(mul_eq_zero.mp z).resolve_right he]
    · have he := hp.2.2 i s hs ht
      cases hb : u i <;> simp only [signBit] <;>
        linear_combination (walsh s u * coefficient s h) * he
  have hz : (∑ s, g s) + (∑ s, g (flip i s)) = 0 := by
    rw [← Finset.sum_add_distrib]
    simp [hneg]
  have he : (∑ s, g (flip i s)) = ∑ s, g s := (flipEquiv i).sum_comp g
  rw [he] at hz
  change ∑ s, g s = 0
  linarith

/-- The specifically displayed matrix, not just the existence of some
matrix in a class. This is the constructive side of Lemma 2. -/
theorem exact_spectral_matrix_eq8 {ι : Type*} {q d : ℕ} {labels : Fin q → ℚ}
    {C : Matrix ι (Cube q) ℚ} {A : Set (Cube q)} (hW : rowSpace C = walshSpace A)
    {p : Cube q → ℚ[X]} (hp : edgeCondition labels A d p) :
    matrixCondition labels C d (literalSpectralMatrix p) := by
  classical
  let D : ℚ := 2^q
  have hd : D ≠ 0 := pow_ne_zero _ (by norm_num)
  refine ⟨?_,?_,?_⟩
  · intro u v
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro s _
    exact (natDegree_C_mul_le _ _).trans (hp.1 s)
  · intro u v
    simp only [literalSpectralMatrix, eval_finset_sum, eval_mul, eval_C, hp.2.1, mul_one, ← Finset.sum_div]
    have h : (∑ s : Cube q, walsh s u * walsh s v) = if u = v then D else 0 := by
      calc
        _ = ∑ s : Cube q, walsh u s * walsh v s := by
          apply Finset.sum_congr rfl
          intro s _
          rw [walsh_comm s u, walsh_comm s v]
        _ = _ := walsh_orthogonal u v
    rw [h]
    split <;> simp_all [D]
  · intro u i h hk hh
    have hn := spectral_edge_sum hp u i h ((kernel_walsh hW h).mp hk) hh
    calc
      _ = (∑ s : Cube q, (p s).eval (labels i) * walsh s u * coefficient s h) / (2:ℚ)^q := by
        simp only [literalSpectralMatrix, eval_finset_sum, eval_mul, eval_C, Finset.sum_mul]
        rw [Finset.sum_comm]
        simp only [coefficient, Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro s _
        apply Finset.sum_congr rfl
        intro v _
        ring
      _ = 0 := by rw [hn, zero_div]

/-- The exact original matrix scheme for (13): measured Walsh vertices are
precisely the literal layer set, with the original cost and polynomial. -/
theorem literal_periodic_matrix_scheme {γ : ℝ} (hγ : 1/2 < γ) :
    ∀ᶠ q : ℕ in atTop,
      let l := literalCut γ q
      let K := literalPeriodicLayers q l
      let d := literalPeriod q l-2
      ∃ m : ℕ, m = (∑ k ∈ K, q.choose k) ∧ (m:ℝ) ≤ measurementBudget q γ ∧
        ∃ C : Matrix (Fin m) (Cube q) ℚ,
          Ternary C ∧ rowSpace C = walshSpace (layerFamily q K) ∧
            FlipInvariant (rowSpace C) ∧ PermInvariant (rowSpace C) ∧
              matrixCondition (printedLabels q) C d
                (literalSpectralMatrix (literalRunPolynomials (printedLabels q) K)) := by
  classical
  filter_upwards [literal_periodic_layers_fit_printed_budget γ hγ, literal_cut_rounding γ hγ]
    with q hc hr
  let l := literalCut γ q
  let K := literalPeriodicLayers q l
  let A := Finset.univ.filter (fun s : Cube q => weight s ∈ K)
  have hA : (↑A : Set (Cube q)) = layerFamily q K := by
    ext s
    simp [A, layerFamily]
  have hcard : A.card = ∑ k ∈ K, q.choose k := by
    unfold A
    rw [← Finset.sum_card_fiberwise_eq_card_filter Finset.univ K weight]
    simp_rw [layer_size]
  have hcost : (A.card:ℝ) ≤ measurementBudget q γ := by
    rw [hcard]
    push_cast
    exact hc.1
  obtain ⟨C,hT,hW⟩ := arbitrary_family_row_realization A
  rw [hA] at hW
  have hK : K ⊆ Finset.range (q+1) := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (mem_literalPeriodicLayers.mp hk).1)
  have comm := (symmetric_spaces (rowSpace C)).mpr ⟨K,hK,hW⟩
  have poly := literal_run_polynomials_satisfy_eq9 (a := printedLabels q) printedLabels_nonzero K
  change edgeCondition _ _ (maxGap q (literalPeriodicLayers q l)) _ at poly
  rw [literal_periodic_gap hr.1] at poly
  exact ⟨A.card,hcard,hcost,C,hT,hW,comm.1,comm.2,exact_spectral_matrix_eq8 hW poly⟩

end
end LocalReconstruction.Paper1Coverage

#print axioms LocalReconstruction.Paper1Coverage.exact_spectral_matrix_eq8
#print axioms LocalReconstruction.Paper1Coverage.literal_periodic_matrix_scheme
