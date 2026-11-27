import BooleanCube.SymmetricLayers
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.ModEq

/-! Paper 1, (11): the particular residue class through the printed cutoff,
as opposed to independently choosing a cheaper class in the tails. -/

namespace LocalReconstruction.Paper1Coverage

open Finset

def literalPeriod (q l : ℕ) : ℕ := q-2*l

def literalPeriodicLayers (q l : ℕ) : Finset ℕ :=
  (range (q+1)).filter fun k => l % literalPeriod q l = k % literalPeriod q l

theorem mem_literalPeriodicLayers {q l k : ℕ} :
    k ∈ literalPeriodicLayers q l ↔ k ≤ q ∧ l ≡ k [MOD literalPeriod q l] := by
  simp [literalPeriodicLayers, Nat.ModEq]

/-- The exact signed progression in (11), intersected with `[0,q]`. -/
theorem mem_literal_periodic_eq11 {q l k : ℕ} :
    k ∈ literalPeriodicLayers q l ↔
      k ≤ q ∧ ∃ j : ℤ, (k:ℤ) = (l:ℤ) + j * (literalPeriod q l : ℤ) := by
  rw [mem_literalPeriodicLayers, Nat.modEq_iff_dvd]
  constructor
  · rintro ⟨hk,j,hj⟩
    refine ⟨hk,j,?_⟩
    rw [mul_comm] at hj
    omega
  · rintro ⟨hk,j,hj⟩
    refine ⟨hk,j,?_⟩
    calc
      (k:ℤ)-l = j * (literalPeriod q l : ℤ) := by omega
      _ = (literalPeriod q l : ℤ) * j := mul_comm _ _

theorem literal_period_positive {q l : ℕ} (hl : 2*l < q) : 0 < literalPeriod q l := by
  unfold literalPeriod
  omega

private theorem literal_period_cast {q l : ℕ} (hl : 2*l < q) :
    (literalPeriod q l : ℤ) = (q:ℤ)-2*(l:ℤ) := by
  unfold literalPeriod
  rw [Nat.cast_sub (by omega), Nat.cast_mul]
  rfl

theorem literal_periodic_centers {q l : ℕ} (hl : 2*l < q) :
    l ∈ literalPeriodicLayers q l ∧ q-l ∈ literalPeriodicLayers q l := by
  constructor
  · exact mem_literal_periodic_eq11.mpr ⟨by omega, 0, by simp⟩
  · apply mem_literal_periodic_eq11.mpr
    refine ⟨by omega, 1,?_⟩
    rw [one_mul, literal_period_cast hl, Nat.cast_sub (by omega)]
    ring

theorem literal_periodic_reflect {q l k : ℕ} (hl : 2*l < q)
    (hk : k ∈ literalPeriodicLayers q l) : q-k ∈ literalPeriodicLayers q l := by
  obtain ⟨hkq,j,hj⟩ := mem_literal_periodic_eq11.mp hk
  refine mem_literal_periodic_eq11.mpr ⟨by omega,1-j,?_⟩
  rw [Nat.cast_sub hkq, sub_mul, one_mul]
  have h := literal_period_cast hl
  omega

theorem no_literal_periodic_between_centers {q l k : ℕ} (hl : 2*l < q)
    (hlk : l < k) (hkr : k < q-l) : k ∉ literalPeriodicLayers q l := by
  intro hk
  obtain ⟨_,j,hj⟩ := mem_literal_periodic_eq11.mp hk
  have hp : 0 < (literalPeriod q l : ℤ) := by exact_mod_cast literal_period_positive hl
  have hsign : 0 < j := by
    by_contra! h
    have hnon := mul_nonpos_of_nonpos_of_nonneg h hp.le
    omega
  have lower := mul_le_mul_of_nonneg_right (show (1:ℤ) ≤ j by omega) hp.le
  rw [one_mul] at lower
  have period := literal_period_cast hl
  omega

private theorem some_residue_in_each_period (L : ℕ) {h r : ℕ} (hr : r < h) :
    ∃ k, L ≤ k ∧ k < L+h ∧ k % h = r := by
  let p := fun k : ℕ => k % h = r
  have period : Function.Periodic p h := fun k => congrArg (· = r) (Nat.add_mod_right k h)
  have hc := Nat.filter_Ico_card_eq_of_periodic L h p period
  have pos : 0 < h.count p := by
    rw [Nat.count_eq_card_filter_range]
    exact card_pos.mpr ⟨r, mem_filter.mpr ⟨mem_range.mpr hr, Nat.mod_eq_of_lt hr⟩⟩
  rw [← hc] at pos
  obtain ⟨k, hk⟩ := card_pos.mp pos
  exact ⟨k, (mem_Ico.mp (mem_filter.mp hk).1).1,
    (mem_Ico.mp (mem_filter.mp hk).1).2, (mem_filter.mp hk).2⟩

/-- The largest retained endpoint difference of the paper's actual full class
is exactly `h-2` (with natural subtraction when the retained set is empty). -/
theorem literal_periodic_gap {q l : ℕ} (hl : 2*l < q) :
    maxGap q (literalPeriodicLayers q l) = literalPeriod q l-2 := by
  apply le_antisymm
  · apply (maxGap_le_iff q _ _).mpr
    intro L U hLU hU hclear
    by_contra! bad
    obtain ⟨k,hL,hk,hr⟩ := some_residue_in_each_period L
      (Nat.mod_lt l (literal_period_positive hl))
    have kU : k ≤ U := by omega
    exact hclear k hL kU (mem_literalPeriodicLayers.mpr ⟨kU.trans hU, hr.symm⟩)
  · by_cases hn : literalPeriod q l ≤ 1
    · have hz : literalPeriod q l-2 = 0 := by omega
      rw [hz]
      exact Nat.zero_le _
    have hg := (maxGap_le_iff q (maxGap q (literalPeriodicLayers q l)) _).mp le_rfl
    have hit := hg (l+1) (q-l-1) (by unfold literalPeriod at hn; omega) (by omega)
      (fun x hx₁ hx₂ => no_literal_periodic_between_centers hl (by omega) (by omega))
    unfold literalPeriod
    omega

end LocalReconstruction.Paper1Coverage

#print axioms LocalReconstruction.Paper1Coverage.mem_literalPeriodicLayers
#print axioms LocalReconstruction.Paper1Coverage.mem_literal_periodic_eq11
#print axioms LocalReconstruction.Paper1Coverage.literal_periodic_centers
#print axioms LocalReconstruction.Paper1Coverage.literal_periodic_reflect
#print axioms LocalReconstruction.Paper1Coverage.no_literal_periodic_between_centers
#print axioms LocalReconstruction.Paper1Coverage.literal_periodic_gap
