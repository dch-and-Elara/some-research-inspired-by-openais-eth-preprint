import P5ObservationLength

/-! Finite layer sum of (A.11). The index j starts at zero, so
"j < precision" is literally "s ≥ 1, precision ≥ s" for s=j+1.
The local precision-times-nullity estimates and the determinant budget
are independent premises of this assembly lemma. -/
namespace Paper5
open scoped BigOperators

variable {T : Type*} [Fintype T]

theorem precision_layer_sum (P d : T→ℕ) :
    (∑ t,d t*P t) =
      ∑ j ∈ Finset.range (Finset.univ.sup P),
        ∑ t ∈ Finset.univ.filter (fun t => j<P t), d t := by
  classical
  let U := Finset.univ.sup P
  have h (t : T) : (Finset.range U).filter (fun j => j<P t) = Finset.range (P t) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_range]
    have hu : P t≤U := Finset.le_sup (Finset.mem_univ t)
    omega
  calc
    (∑ t,d t*P t) = ∑ t, ∑ j ∈ (Finset.range U).filter (fun j => j<P t), d t := by
      apply Finset.sum_congr rfl
      intro t _
      rw [h]
      simp [Nat.mul_comm]
    _ = ∑ j ∈ Finset.range U, ∑ t ∈ Finset.univ.filter (fun t => j<P t), d t := by
      simp only [Finset.sum_filter]
      exact Finset.sum_comm

theorem precision_layer_budget (P k d : T→ℕ) (N D : ℕ)
    (hwidth : ∀ t,d t ≤ N*k t) (hdet : (∑ t,d t)≤D)
    (loss : T→ENat) (hloss : ∀ t,loss t≤(d t*P t:ℕ)) :
    (∑ t,loss t) ≤
      (↑(∑ j ∈ Finset.range (Finset.univ.sup P),
        min D (N * ∑ t ∈ Finset.univ.filter (fun t => j<P t),k t)) : ENat) := by
  classical
  calc
    (∑ t,loss t) ≤ ∑ t, ((d t*P t:ℕ):ENat) := Finset.sum_le_sum fun t _ => hloss t
    _ = ((∑ t,d t*P t):ℕ) := by simp
    _ ≤ ↑(∑ j ∈ Finset.range (Finset.univ.sup P),
        min D (N * ∑ t ∈ Finset.univ.filter (fun t => j<P t),k t)) := by
      apply ENat.coe_le_coe.mpr
      rw [precision_layer_sum]
      apply Finset.sum_le_sum
      intro j _
      apply le_min
      · exact (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans hdet
      · rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun t _ => hwidth t

#print axioms precision_layer_sum
#print axioms precision_layer_budget
end Paper5
