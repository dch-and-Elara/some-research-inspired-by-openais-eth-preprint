import BooleanCube.Asymmetric
import BooleanCube.WeightedTail

namespace LocalReconstruction
noncomputable section
open Finset

private def layerPrefix (q k : ℕ) : ℝ :=
  ∑ j ∈ range (k+1), (q.choose j : ℝ)

private theorem weightedTail_succ (q k : ℕ) :
    weightedTail q (k+1) = weightedTail q k + layerPrefix q (k+1) := by
  unfold weightedTail layerPrefix
  rw [sum_range_succ _ (k+1), sum_range_succ (fun j => (q.choose j : ℝ)) (k+1)]
  simp only [Nat.add_sub_cancel_left, Nat.cast_one, one_mul]
  rw [← add_assoc, ← sum_add_distrib]
  congr 1
  apply sum_congr rfl
  intro j hj
  rw [show k+1+1-j = (k+1-j)+1 by have := mem_range.mp hj; omega, Nat.cast_add]
  push_cast
  ring

private theorem weightedTail_prefix (q k : ℕ) :
    weightedTail q k = ∑ j ∈ range (k+1), layerPrefix q j := by
  induction k with
  | zero => simp [weightedTail, layerPrefix]
  | succ k ih => rw [weightedTail_succ, ih, sum_range_succ (layerPrefix q) (k+1)]

private theorem weightedTail_add (q k L : ℕ) :
    weightedTail q (k+L) = weightedTail q k +
      ∑ j ∈ range L, layerPrefix q (k+1+j) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Nat.add_succ, weightedTail_succ, ih, sum_range_succ, add_assoc, Nat.add_right_comm k L 1]

/-- Reflecting the last L terms of the finite bilinear sum gives a second
copy of the weighted tail, with its endpoint and a lower prefix removed. -/
theorem asymmetric_reflected_budget {q d k L : ℕ} {γ : ℝ}
    (h : realAsymmetricScheme q d γ) (hr : d + 2*k < q) (hL : L < k) :
    weightedTail q k + weightedTail q (k-1) - weightedTail q (k-L-1) ≤
      ((k+L+1 : ℕ) : ℝ) * measurementBudget q γ := by
  have hb := asymmetric_bilinear_budget (r := 2*k) (K := k+L) h hr (by omega)
  change (∑ j ∈ range (k+L+1), layerPrefix q (min j (2*k-j))) ≤ _ at hb
  have hsplit : (∑ j ∈ range (k+L+1), layerPrefix q (min j (2*k-j))) =
      weightedTail q k + ∑ j ∈ range L, layerPrefix q (k-1-j) := by
    rw [show k+L+1 = (k+1)+L by omega, sum_range_add, weightedTail_prefix]
    congr 1
    · apply sum_congr rfl
      intro j hj
      have := mem_range.mp hj
      rw [show min j (2*k-j) = j by omega]
    · apply sum_congr rfl
      intro j hj
      have := mem_range.mp hj
      rw [show min (k+1+j) (2*k-(k+1+j)) = k-1-j by omega]
  rw [hsplit] at hb
  have he := weightedTail_add q (k-L-1) L
  rw [show k-L-1+L = k-1 by omega] at he
  rw [← sum_range_reflect] at he
  have hs : (∑ j ∈ range L, layerPrefix q (k-L-1+1+(L-1-j))) =
      ∑ j ∈ range L, layerPrefix q (k-1-j) := by
    apply sum_congr rfl
    intro j hj
    have := mem_range.mp hj
    congr 1
    omega
  rw [hs] at he
  linarith

end
end LocalReconstruction

