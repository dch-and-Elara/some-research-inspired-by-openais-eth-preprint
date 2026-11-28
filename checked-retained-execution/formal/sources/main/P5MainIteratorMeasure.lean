import P5MainIteratorFrame
import P5MainIteratorOccupied
import P5MainIteratorWeights
import P5MainIteratorCast

/-! Actual raw grouped measurement, its orthogonal normalization, and the
exact weighted column energy of the occupied incidence chart. -/
namespace P5MainIterator
open scoped BigOperators RealInnerProductSpace Classical

variable {O E V : Type*} (A : O → Type*) [Fintype O] [∀ o, Fintype (A o)]
  [Fintype E] [Fintype V]

noncomputable def rawRows (keep : ℕ → Prop) :
    Matrix (Exceptional A keep) (OrbitSlots A) ℚ :=
  Matrix.of fun r s => qOrbitRow A r.val s

noncomputable def embeddingMatrix (L : Placement E V (OrbitSlots A)) :
    Matrix (OrbitSlots A) V ℚ :=
  Matrix.of fun s v => if s ∈ filled L v then 1 else 0

noncomputable def rawMeasurement (keep : ℕ → Prop)
    (L : Placement E V (OrbitSlots A)) : Matrix (Exceptional A keep) V ℚ :=
  rawRows A keep * embeddingMatrix A L

omit [Fintype V] in
theorem rawMeasurement_apply (keep : ℕ → Prop) (L : Placement E V (OrbitSlots A))
    (r : Exceptional A keep) (v : V) :
    rawMeasurement A keep L r v = ∑ s ∈ filled L v, qOrbitRow A r.val s := by
  rw [rawMeasurement,Matrix.mul_apply]
  symm
  apply Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _)
  · intro s hs
    simp [rawRows,embeddingMatrix,(Finset.mem_sdiff.mp hs).2]
  · intro s hs
    simp [rawRows,embeddingMatrix,hs]

noncomputable def measured (keep : ℕ → Prop) (L : Placement E V (OrbitSlots A)) :
    Matrix (Exceptional A keep) V ℝ :=
  Matrix.of fun r v => ⟪orbitVector A r.val, occupiedColumn L v⟫

omit [Fintype V] in
theorem measured_apply (keep : ℕ → Prop) (L : Placement E V (OrbitSlots A))
    (r : Exceptional A keep) (v : V) :
    measured A keep L r v =
      ∑ s ∈ filled L v, orbitRow A r.val s * columnScale L v := by
  change ⟪orbitVector A r.val,occupiedColumn L v⟫ = _
  rw [EuclideanSpace.inner_eq_star_dotProduct,dotProduct]
  symm
  apply Finset.sum_subset_zero_on_sdiff (Finset.subset_univ _)
  · intro s hs
    simp [occupiedColumn,(Finset.mem_sdiff.mp hs).2]
  · intro s hs
    simp [orbitVector,occupiedColumn,hs,mul_comm]

noncomputable def rowScale (r : OrbitSlots A) : ℝ :=
  (Real.sqrt ((2:ℝ)^Fintype.card (A r.1)))⁻¹

theorem measured_factorization (keep : ℕ → Prop) (L : Placement E V (OrbitSlots A)) :
    measured A keep L =
      Matrix.diagonal (fun r : Exceptional A keep => rowScale A r.val) *
      (rawMeasurement A keep L).map (Rat.castHom ℝ) *
      Matrix.diagonal (columnScale L) := by
  ext r v
  rw [measured_apply,Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.map_apply,
      rawMeasurement_apply]
  change _ = rowScale A r.val * ((∑ s ∈ filled L v, qOrbitRow A r.val s : ℚ):ℝ) * columnScale L v
  rw [Rat.cast_sum,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [orbitRow_normalizes]
  rfl

theorem measured_rank_le (keep : ℕ → Prop) (L : Placement E V (OrbitSlots A)) :
    (measured A keep L).rank ≤ (rawMeasurement A keep L).rank := by
  rw [measured_factorization]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_mul_le_right _ _).trans (rank_map_le _ _))

omit [Fintype V] in
theorem measured_energy_at (keep : ℕ → Prop) (L : Placement E V (OrbitSlots A)) (v : V)
    (hunique : ∀ s ∈ filled L v, ∀ t ∈ filled L v, s.1=t.1 → s=t) :
    (∑ r : Exceptional A keep,(measured A keep L r v)^2) =
      (∑ s ∈ filled L v, binomialMass (Fintype.card (A s.1)) keep) / (filled L v).card := by
  have hterm (r : Exceptional A keep) :
      (measured A keep L r v)^2 =
        ∑ s ∈ filled L v, (orbitRow A r.val s * columnScale L v)^2 := by
    rw [measured_apply]
    refine sum_sq_when_unique _ _ (fun s hs t ht h₁ h₂ => ?_)
    have a : r.val.1=s.1 := by
      by_contra hn
      exact h₁ (by simp [orbitRow_off A _ _ hn])
    have b : r.val.1=t.1 := by
      by_contra hn
      exact h₂ (by simp [orbitRow_off A _ _ hn])
    exact hunique s hs t ht (a.symm.trans b)
  simp only [hterm]
  rw [Finset.sum_comm,div_eq_mul_inv,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  simp_rw [mul_pow,columnScale_square,← Finset.sum_mul,exceptional_slot_energy]

set_option maxHeartbeats 6400000 in
theorem orbit_attainable_rank (keep : ℕ → Prop) (L : Placement E V (OrbitSlots A))
    (hunique : ∀ v, ∀ s ∈ filled L v, ∀ t ∈ filled L v, s.1=t.1 → s=t) :
    (∑ v, (∑ s ∈ filled L v, binomialMass (Fintype.card (A s.1)) keep) / (filled L v).card)
      ≤ ((rawMeasurement A keep L).rank : ℝ) := by
  have h := orthonormal_frame_rank (fun r : Exceptional A keep => orbitVector A r.val)
    (occupiedColumn L) (exceptional_orthonormal A keep) (occupied_orthonormal L)
  change (∑ v, ∑ r : Exceptional A keep, (measured A keep L r v)^2) ≤ _ at h
  simp_rw [measured_energy_at A keep L _ (hunique _)] at h
  exact h.trans (by exact_mod_cast (measured_rank_le A keep L))

#print axioms rawMeasurement_apply
#print axioms measured_apply
#print axioms measured_factorization
#print axioms measured_rank_le
#print axioms measured_energy_at
#print axioms orbit_attainable_rank
end P5MainIterator
