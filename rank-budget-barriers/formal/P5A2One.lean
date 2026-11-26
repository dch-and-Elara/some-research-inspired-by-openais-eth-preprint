import P5A2Powers
import P5A2Rank

/-! Paper 5, A2 exactly: the Hankel entries and cutoff come from a
linear functional on the actual truncated polynomial algebra. -/
namespace P5A2
open Polynomial Matrix Module
open scoped Classical BigOperators

variable {K : Type*} [Field K]

noncomputable def coeffSequence (k : ℕ) (read : Trunc K k →ₗ[K] K) (j : ℕ) : K :=
  if h : j<k then read (powers K k ⟨j,h⟩) else 0

theorem one_pairing_hankel (k : ℕ) (read : Trunc K k →ₗ[K] K) :
    pairing (powers K k) read = hankel k (coeffSequence k read) := by
  apply Matrix.ext
  intro i j
  change read (powers K k i * powers K k j) =
    if i.val+j.val<k then coeffSequence k read (i.val+j.val) else 0
  rw [powers_mul]
  by_cases h : i.val+j.val<k
  · simp [h,coeffSequence]
  · simp [h]

theorem one_pairing_rank_of_last (k : ℕ) (read : Trunc K k →ₗ[K] K)
    (r : Fin k) (h : read (powers K k r) ≠ 0)
    (ht : ∀ j : Fin k, r < j → read (powers K k j) = 0) :
    (pairing (powers K k) read).rank = r.val+1 := by
  rw [one_pairing_hankel]
  apply hankel_rank_of_last _ r
  · simpa [coeffSequence,r.isLt] using h
  · intro j hj hk
    simpa [coeffSequence,hk] using ht ⟨j,hk⟩ hj

theorem one_pairing_zero (k : ℕ) :
    (pairing (powers K k) (0 : Trunc K k →ₗ[K] K)).rank = 0 := by
  have h : pairing (powers K k) (0 : Trunc K k →ₗ[K] K) = 0 := by
    apply Matrix.ext
    intro i j
    simp [pairing]
  rw [h,Matrix.rank_zero]

/-- For any nonzero linear readout the actual highest nonzero coefficient
exists, without an extra hypothesis selecting it. -/
theorem one_pairing_rank (k : ℕ) (read : Trunc K k →ₗ[K] K) (hn : read ≠ 0) :
    ∃ r : Fin k, read (powers K k r) ≠ 0 ∧
      (∀ j : Fin k, r<j → read (powers K k j) = 0) ∧
      (pairing (powers K k) read).rank = r.val+1 := by
  have hb : ∃ i : Fin k, read (powers K k i) ≠ 0 := by
    by_contra! h
    apply hn
    apply (powers K k).ext
    intro j
    simpa using h j
  let S : Finset (Fin k) := Finset.univ.filter (fun j => read (powers K k j) ≠ 0)
  have hS : S.Nonempty := by
    obtain ⟨i,hi⟩ := hb
    exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  let r := S.max' hS
  have hz : read (powers K k r) ≠ 0 := (Finset.mem_filter.mp (S.max'_mem hS)).2
  have ht (j : Fin k) (hj : r < j) : read (powers K k j) = 0 := by
    by_contra! hw
    have hm : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩
    exact (not_le_of_gt hj) (S.le_max' j hm)
  exact ⟨r,hz,ht,one_pairing_rank_of_last k read r hz ht⟩

#print axioms one_pairing_hankel
#print axioms one_pairing_rank_of_last
#print axioms one_pairing_zero
#print axioms one_pairing_rank
end P5A2
