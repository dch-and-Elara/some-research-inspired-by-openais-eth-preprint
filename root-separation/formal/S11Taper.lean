
import S11Schedule

namespace S11

open scoped BigOperators

/-- The L odd grid points in a complete grid of 2L consecutive integers,
    indexed in order for an even L. -/
def oddGridPoint {L : ℕ} (j : Fin L) : ℤ := -(L : ℤ) + 2*(j.val : ℤ) + 1

theorem oddGridPoint_level {L : ℕ} (hL : Even L) (j : Fin L) :
    level (oddGridPoint j) = 0 := by
  change padicValInt 2 (oddGridPoint j) = 0
  apply padicValInt.eq_zero_of_not_dvd
  rintro ⟨b, hb⟩
  obtain ⟨c,hc⟩ := hL
  unfold oddGridPoint at hb
  omega

theorem oddGridPoint_active {u L : ℕ} (hu : 0 < u) (hL : Even L) (j : Fin L) :
    oddGridPoint j ∈ centers u L := by
  simp only [centers, Finset.mem_filter, Finset.mem_Ico, oddGridPoint_level hL, hu, and_true]
  have hj := j.isLt
  obtain ⟨c,hc⟩ := hL
  unfold oddGridPoint
  omega

theorem taper_degree_window {u M L : ℕ} (hu : 0 < u) (hM : 0 < M) (hL : 0 < L)
    (heven : Even L) :
    M*(2*L-1) < ∑ t ∈ centers u L, multiplicity M u t := by
  let emb : Fin L ↪ ℤ := ⟨oddGridPoint, by
    intro i j hij
    apply Fin.ext
    unfold oddGridPoint at hij
    omega⟩
  let odds := Finset.univ.map emb
  have hs : odds ⊆ centers u L := by
    intro t ht
    obtain ⟨j,_,rfl⟩ := Finset.mem_map.1 ht
    exact oddGridPoint_active hu heven j
  calc
    M * (2*L-1) < L * (3*M) := by
      have hm := Nat.mul_pos hM hL
      have h₂ : M * (2*L-1) ≤ M*(2*L) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      have h3 : M*(2*L) = 2*(M*L) := by ring
      have h4 : L*(3*M) = 3*(M*L) := by ring
      omega
    _ ≤ L * (taper M u * u) := Nat.mul_le_mul_left _ (three_mul_le_taper_mul hu)
    _ = ∑ t ∈ odds, multiplicity M u t := by
      rw [Finset.sum_map]
      change _ = ∑ j : Fin L, multiplicity M u (oddGridPoint j)
      simp [multiplicity, oddGridPoint_level heven]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.zero_le _)

#print axioms oddGridPoint_level
#print axioms oddGridPoint_active
#print axioms taper_degree_window

end S11

