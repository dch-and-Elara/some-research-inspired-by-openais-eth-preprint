import J7PrintedParamsRoot
import J1PPrintedMesh

/-! The exact J7 packing guards use the same root scale as the printed
recursive program, not an independently changed threshold or bit width. -/
namespace J7R13
open scoped BigOperators
open J7PrintedParams J1PPrinted
noncomputable section

theorem root_delta_same (s : ℕ) : rootDelta s = sourceDelta s := rfl

theorem root_width_same (s : ℕ) : stepU (Nat.clog 2 s) 0 = rootU s := by
  rw [stepU_as_div,pow_zero,Nat.div_one]
  rfl

theorem root_bits_same (s : ℕ) (hu : 0 < rootU s) :
    stepA (Nat.clog 2 s) 0 = rootT s+1 := by
  simp only [stepA,zero_add,Finset.range_one,Finset.sum_singleton,root_width_same,root_exponent s hu]

theorem root_cells_same (s : ℕ) (hu : 0 < rootU s) :
    stepD (Nat.clog 2 s) 0 = printedD (rootT s) := by
  rw [stepD,root_bits_same s hu]
  rfl

theorem root_slots_same (s : ℕ) (hu : 0 < rootU s) :
    stepL (Nat.clog 2 s) 0 = printedL (rootT s) := by
  rw [stepL,root_bits_same s hu]
  rfl

theorem root_cutoff_same (s : ℕ) (hlog : 0 < Nat.clog 2 s) :
    leafThreshold s = J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) := by
  let d := Nat.sqrt (Nat.clog 2 s)
  have hd : 0 < d := Nat.sqrt_pos.2 hlog
  have hdq : (0:ℚ) < d := by exact_mod_cast hd
  change Nat.ceil ((s:ℚ)/d) = (s+d-1)/d
  apply le_antisymm
  · apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hdq).2
    exact_mod_cast J9PrintedSchedule.le_roundup_mul s d hd
  · let q := Nat.ceil ((s:ℚ)/d)
    have hq : s ≤ q*d := by
      have h := (div_le_iff₀ hdq).mp (Nat.le_ceil ((s:ℚ)/d))
      exact_mod_cast h
    change (s+d-1)/d ≤ q
    apply Nat.lt_succ_iff.mp
    apply (Nat.div_lt_iff_lt_mul hd).mpr
    rw [Nat.succ_mul]
    omega

#print axioms root_delta_same
#print axioms root_width_same
#print axioms root_bits_same
#print axioms root_cells_same
#print axioms root_slots_same
#print axioms root_cutoff_same
end
end J7R13
