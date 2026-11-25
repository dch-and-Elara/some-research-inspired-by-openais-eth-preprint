import Mathlib.Data.Rat.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-! A finite rational second-moment and union-bound selection principle.
No independence is assumed here: a caller must establish the stated moments
for its actual random experiment. -/

namespace FiniteSelection

open scoped BigOperators
open scoped Classical

variable {Ω J : Type*} [Fintype Ω] [Fintype J]

theorem exists_avoid_bad (μ : Ω → ℚ) (bad : J → Ω → Prop) (budget : J → ℚ)
    (hμ : ∀ ω, 0 ≤ μ ω) (hmass : ∑ ω, μ ω = 1)
    (hbad : ∀ j, (∑ ω, if bad j ω then μ ω else 0) ≤ budget j)
    (hbudget : ∑ j, budget j < 1) :
    ∃ ω, 0 < μ ω ∧ ∀ j, ¬bad j ω := by
  classical
  by_contra h
  push_neg at h
  have hpoint (ω : Ω) : μ ω ≤ ∑ j, if bad j ω then μ ω else 0 := by
    by_cases hp : 0 < μ ω
    · obtain ⟨j, hj⟩ := h ω hp
      have hs := Finset.single_le_sum
        (fun k (_ : k ∈ (Finset.univ : Finset J)) =>
          show (0 : ℚ) ≤ (if bad k ω then μ ω else 0) by
            split_ifs
            · exact hμ ω
            · exact le_rfl)
        (Finset.mem_univ j)
      simpa only [if_pos hj] using hs
    · have hz : μ ω = 0 := le_antisymm (not_lt.mp hp) (hμ ω)
      simp [hz]
  have htotal : (1 : ℚ) ≤ ∑ j, budget j := by
    calc
      1 = ∑ ω, μ ω := hmass.symm
      _ ≤ ∑ ω, ∑ j, if bad j ω then μ ω else 0 :=
        Finset.sum_le_sum fun ω _ => hpoint ω
      _ = ∑ j, ∑ ω, if bad j ω then μ ω else 0 := Finset.sum_comm
      _ ≤ ∑ j, budget j := Finset.sum_le_sum fun j _ => hbad j
  exact (not_lt_of_ge htotal) hbudget

theorem tail_mass_le (μ Y : Ω → ℚ) (a margin variance : ℚ)
    (hμ : ∀ ω, 0 ≤ μ ω) (hmargin : 0 < margin)
    (hmoment : ∑ ω, μ ω * (Y ω - a) ^ 2 ≤ variance) :
    (∑ ω, if margin ≤ |Y ω - a| then μ ω else 0) ≤ variance / margin ^ 2 := by
  have hpoint (ω : Ω) :
      (if margin ≤ |Y ω - a| then μ ω else 0) * margin ^ 2 ≤
        μ ω * (Y ω - a) ^ 2 := by
    split_ifs with hb
    · have hs : margin ^ 2 ≤ (Y ω - a) ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ hmargin.le (abs_nonneg _)).mpr hb
      exact mul_le_mul_of_nonneg_left hs (hμ ω)
    · simp only [zero_mul]
      exact mul_nonneg (hμ ω) (sq_nonneg _)
  apply (le_div_iff₀ (sq_pos_of_pos hmargin)).mpr
  calc
    _ = ∑ ω, (if margin ≤ |Y ω - a| then μ ω else 0) * margin ^ 2 :=
      Finset.sum_mul _ _ _
    _ ≤ ∑ ω, μ ω * (Y ω - a) ^ 2 := Finset.sum_le_sum fun ω _ => hpoint ω
    _ ≤ variance := hmoment

theorem exists_simultaneous_close (μ : Ω → ℚ) (Y : J → Ω → ℚ)
    (a margin variance : J → ℚ)
    (hμ : ∀ ω, 0 ≤ μ ω) (hmass : ∑ ω, μ ω = 1)
    (hmargin : ∀ j, 0 < margin j)
    (hmoment : ∀ j, ∑ ω, μ ω * (Y j ω - a j) ^ 2 ≤ variance j)
    (hbudget : ∑ j, variance j / margin j ^ 2 < 1) :
    ∃ ω, 0 < μ ω ∧ ∀ j, |Y j ω - a j| < margin j := by
  classical
  obtain ⟨ω, hw, hall⟩ := exists_avoid_bad μ
    (fun j ω => margin j ≤ |Y j ω - a j|)
    (fun j => variance j / margin j ^ 2) hμ hmass
    (fun j => by
      convert (tail_mass_le μ (Y j) (a j) (margin j) (variance j)
        hμ (hmargin j) (hmoment j)) using 1
      congr 1
      funext ω
      by_cases hb : margin j ≤ |Y j ω - a j| <;> simp [hb]) hbudget
  exact ⟨ω, hw, fun j => not_le.mp (hall j)⟩

theorem exists_simultaneous_large (μ : Ω → ℚ) (Y : J → Ω → ℚ)
    (a margin variance : J → ℚ)
    (hμ : ∀ ω, 0 ≤ μ ω) (hmass : ∑ ω, μ ω = 1)
    (hmargin : ∀ j, 0 < margin j)
    (hmoment : ∀ j, ∑ ω, μ ω * (Y j ω - a j) ^ 2 ≤ variance j)
    (hbudget : ∑ j, variance j / margin j ^ 2 < 1)
    (hmean : ∀ j, 2 * margin j ≤ |a j|) :
    ∃ ω, 0 < μ ω ∧ ∀ j, margin j < |Y j ω| := by
  obtain ⟨ω, hw, hall⟩ := exists_simultaneous_close μ Y a margin variance
    hμ hmass hmargin hmoment hbudget
  refine ⟨ω, hw, fun j => ?_⟩
  have htriangle : |a j| ≤ |Y j ω - a j| + |Y j ω| := by
    have ht := abs_add_le (a j - Y j ω) (Y j ω)
    rw [abs_sub_comm (a j) (Y j ω)] at ht
    simpa only [sub_add_cancel] using ht
  linarith [hall j, hmean j]

#print axioms exists_avoid_bad
#print axioms tail_mass_le
#print axioms exists_simultaneous_close
#print axioms exists_simultaneous_large

end FiniteSelection
