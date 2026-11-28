import P9GuardedPacking

/-! Simultaneous two-sign endpoint marking and a nonnegative conflict statistic. -/
namespace Paper6JointSeating
open scoped BigOperators
open GuardExpectation GuardedPacking

theorem uniform_joint_potential {E I : Type*} [Fintype E] [DecidableEq E]
    [Fintype I] {L : ℕ} (hL : 2 ≤ L)
    (side : I → Bool) (d : I → E → ℚ) :
    ∃ a : E → Fin L,
      (∑ i, (centeredLoad (L : ℚ)⁻¹ (signSymbol L hL (side i)) (d i) a)^2)
       ≤ (L : ℚ)⁻¹ * (1 - (L : ℚ)⁻¹) * ∑ i, ∑ e, (d i e)^2 := by
  have hl : 0 < L := by omega
  letI : Nonempty (Fin L) := ⟨⟨0, hl⟩⟩
  obtain ⟨a, ha⟩ := exists_sample_by_conditioning (uniform E L)
    (fun e b => by unfold uniform; positivity) (sum_uniform L hl)
    (fun a => ∑ i, (centeredLoad (L : ℚ)⁻¹ (signSymbol L hL (side i)) (d i) a)^2)
  refine ⟨a, ha.trans_eq ?_⟩
  rw [average_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ =>
    variance_centeredLoad _ (sum_uniform L hl) _ _ (fun _ => rfl) (d i))

theorem centered_cell {E C : Type*} [Fintype E] {L : ℕ}
    (a : E → Fin L) (z : Fin L) (w : E → C → ℕ) (c : C) :
    centeredLoad (L : ℚ)⁻¹ z (fun e => (w e c : ℚ)) a =
      (cellLoad w (markedSet a z) c : ℚ) - (cellLoad w Finset.univ c : ℚ) / L := by
  simpa [cellLoad, div_eq_mul_inv, Nat.cast_sum] using
    GuardAssembly.centered_marked a z (fun e => w e c)

theorem centered_count {E : Type*} [Fintype E] {L : ℕ}
    (a : E → Fin L) (z : Fin L) :
    centeredLoad (L : ℚ)⁻¹ z (fun _ => 1) a =
      ((markedSet a z).card : ℚ) - (Fintype.card E : ℚ) / L := by
  simpa [div_eq_mul_inv] using GuardAssembly.centered_marked a z (fun _ => 1)

theorem squareDeviation_le_sqrt {x B : ℝ} (h : x^2 ≤ B) (hB : 0 ≤ B) :
    x ≤ Real.sqrt B := by
  by_cases hx : x ≤ 0
  · exact hx.trans (Real.sqrt_nonneg _)
  · exact (Real.le_sqrt (le_of_not_ge hx) hB).mpr h

#print axioms uniform_joint_potential
#print axioms centered_cell
#print axioms centered_count
#print axioms squareDeviation_le_sqrt
end Paper6JointSeating
