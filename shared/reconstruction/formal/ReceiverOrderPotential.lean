import ReceiverOrderScore
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace Reconstruction.ColorAlphabet

noncomputable section

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- Clipped volume at an integer level, counted in the rationals. -/
def clippedVolume (s : T → ℕ) (j : ℕ) : ℚ :=
  ∏ i, ((min (s i) j : ℕ) : ℚ)^2

def rate (j : ℕ) : ℚ := ((j : ℚ)-1) / (2*(j : ℚ)-1)

def orderPotential (s : T → ℕ) : ℕ → ℚ
  | 0 => 0
  | j+1 => orderPotential s j + rate (j+1) * (clippedVolume s (j+1) - clippedVolume s j)

private theorem rate_mono {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) : rate a ≤ rate b := by
  have h1 : (1 : ℚ) ≤ a := by exact_mod_cast ha
  have h2 : (a : ℚ) ≤ b := by exact_mod_cast hab
  unfold rate
  apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
  nlinarith

private def clippedRest (s : T → ℕ) (t : T) (j : ℕ) : ℚ :=
  ∏ i ∈ Finset.univ.erase t, ((min (s i) j : ℕ) : ℚ)^2

private theorem clippedRest_nonneg (s : T → ℕ) (t : T) (j : ℕ) :
    0 ≤ clippedRest s t j :=
  Finset.prod_nonneg (fun _ _ => sq_nonneg _)

private theorem clippedRest_mono (s : T → ℕ) (t : T) {i j : ℕ} (h : i ≤ j) :
    clippedRest s t i ≤ clippedRest s t j := by
  apply Finset.prod_le_prod
  · exact fun _ _ => sq_nonneg _
  · intro k _
    have he : ((min (s k) i : ℕ) : ℚ) ≤ ((min (s k) j : ℕ) : ℚ) := by
      exact_mod_cast min_le_min_left (s k) h
    have hz : (0 : ℚ) ≤ (min (s k) i : ℕ) := Nat.cast_nonneg _
    nlinarith [mul_nonneg (sub_nonneg.mpr he) (add_nonneg hz (hz.trans he))]

private def volumeDrop (s : T → ℕ) (t : T) (j : ℕ) : ℚ :=
  clippedVolume s j - clippedVolume (Function.update s t (s t-1)) j

private theorem volumeDrop_eq (s : T → ℕ) (t : T) (hx : 0 < s t) (j : ℕ) :
    volumeDrop s t j = if s t ≤ j then (2*(s t : ℚ)-1) * clippedRest s t j else 0 := by
  have hf (p : T → ℕ) :
      clippedVolume p j = ((min (p t) j : ℕ) : ℚ)^2 * clippedRest p t j := by
    unfold clippedVolume clippedRest
    exact (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ t)).symm
  have hr : clippedRest (Function.update s t (s t - 1)) t j = clippedRest s t j := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [volumeDrop, hf, hf, hr, Function.update_self]
  by_cases h : s t ≤ j
  · rw [if_pos h, min_eq_left h, min_eq_left (by omega : s t-1 ≤ j),
      Nat.cast_sub (by omega : 1 ≤ s t), Nat.cast_one]
    ring
  · rw [if_neg h, min_eq_right (by omega : j ≤ s t),
      min_eq_right (by omega : j ≤ s t-1), sub_self]

private theorem volumeDrop_mono (s : T → ℕ) (t : T) (hx : 0 < s t)
    {i j : ℕ} (h : i ≤ j) : volumeDrop s t i ≤ volumeDrop s t j := by
  rw [volumeDrop_eq s t hx, volumeDrop_eq s t hx]
  have hp : 1 ≤ (s t : ℚ) := by exact_mod_cast hx
  by_cases hi : s t ≤ i
  · rw [if_pos hi, if_pos (hi.trans h)]
    exact mul_le_mul_of_nonneg_left (clippedRest_mono s t h) (by linarith)
  · rw [if_neg hi]
    split_ifs
    · exact mul_nonneg (by linarith) (clippedRest_nonneg s t j)
    · rfl

private theorem volumeDrop_flat (s : T → ℕ) (t : T) (hx : 0 < s t)
    (hmax : ∀ i, s i ≤ s t) {i j : ℕ} (hi : s t ≤ i) (hj : s t ≤ j) :
    volumeDrop s t i = volumeDrop s t j := by
  rw [volumeDrop_eq s t hx, volumeDrop_eq s t hx, if_pos hi, if_pos hj]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  rw [min_eq_left ((hmax k).trans hi), min_eq_left ((hmax k).trans hj)]

private theorem potential_drop (s : T → ℕ) (t : T) (hx : 0 < s t) (m : ℕ) :
    rate (s t) * volumeDrop s t m ≤
      orderPotential s m - orderPotential (Function.update s t (s t-1)) m := by
  induction m with
  | zero =>
    rw [volumeDrop_eq s t hx, if_neg (by omega)]
    simp [orderPotential]
  | succ m ih =>
    simp only [orderPotential]
    have hd : 0 ≤ volumeDrop s t (m+1) - volumeDrop s t m :=
      sub_nonneg.mpr (volumeDrop_mono s t hx (by omega))
    have he : rate (s t) * (volumeDrop s t (m+1) - volumeDrop s t m) ≤
        rate (m+1) * (volumeDrop s t (m+1) - volumeDrop s t m) := by
      by_cases h : s t ≤ m+1
      · exact mul_le_mul_of_nonneg_right (rate_mono hx h) hd
      · rw [volumeDrop_eq s t hx (m+1), if_neg h, volumeDrop_eq s t hx m,
          if_neg (by omega : ¬ s t ≤ m), sub_self, mul_zero, mul_zero]
    unfold volumeDrop at *
    linarith only [ih, he]

private theorem potential_drop_eq (s : T → ℕ) (t : T) (hx : 0 < s t)
    (hmax : ∀ i, s i ≤ s t) (m : ℕ) :
    rate (s t) * volumeDrop s t m =
      orderPotential s m - orderPotential (Function.update s t (s t-1)) m := by
  induction m with
  | zero =>
    rw [volumeDrop_eq s t hx, if_neg (by omega)]
    simp [orderPotential]
  | succ m ih =>
    simp only [orderPotential]
    have he : rate (s t) * (volumeDrop s t (m+1) - volumeDrop s t m) =
        rate (m+1) * (volumeDrop s t (m+1) - volumeDrop s t m) := by
      by_cases hm : s t ≤ m
      · rw [volumeDrop_flat s t hx hmax (by omega : s t ≤ m+1) hm, sub_self, mul_zero, mul_zero]
      · by_cases h : s t = m+1
        · rw [h]
        · rw [volumeDrop_eq s t hx (m+1), if_neg (by omega : ¬ s t ≤ m+1),
            volumeDrop_eq s t hx m, if_neg hm, sub_self, mul_zero, mul_zero]
    unfold volumeDrop at *
    linarith only [ih, he]

/-- The gain never exceeds the decrease of the clipped-volume potential.
An eligible step in a largest remaining coordinate gives equality. -/
theorem greedy_gain (s : T → ℕ) (t : T) (hx : 0 < s t) (m : ℕ)
    (hm : ∀ i, s i ≤ m) :
    let gain := ((s t : ℚ)-1) * ∏ i ∈ Finset.univ.erase t, (s i : ℚ)^2
    let drop := orderPotential s m - orderPotential (Function.update s t (s t-1)) m
    gain ≤ drop ∧ ((∀ i, s i ≤ s t) → gain = drop) := by
  have hg : rate (s t) * volumeDrop s t m =
      ((s t : ℚ)-1) * ∏ i ∈ Finset.univ.erase t, (s i : ℚ)^2 := by
    rw [volumeDrop_eq s t hx m, if_pos (hm t)]
    have hc : clippedRest s t m = ∏ i ∈ Finset.univ.erase t, (s i : ℚ)^2 := by
      apply Finset.prod_congr rfl
      intro i _
      rw [min_eq_left (hm i)]
    rw [hc, rate]
    have h1 : (1 : ℚ) ≤ s t := by exact_mod_cast hx
    have hne : (s t : ℚ) * 2 - 1 ≠ 0 := by linarith
    field_simp [hne] <;> ring
  simp only
  rw [← hg]
  exact ⟨potential_drop s t hx m, fun h => potential_drop_eq s t hx h m⟩

theorem potential_sum (s : T → ℕ) (m : ℕ) :
    orderPotential s m = ∑ j ∈ Finset.range m,
      rate (j+1) * (clippedVolume s (j+1) - clippedVolume s j) := by
  induction m with
  | zero => simp [orderPotential]
  | succ m ih => rw [Finset.sum_range_succ, orderPotential, ih]

end

end Reconstruction.ColorAlphabet
