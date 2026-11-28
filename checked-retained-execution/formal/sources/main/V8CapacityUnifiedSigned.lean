import V8CapacityUnifiedU7

/-! Identify the power ratio in U7 with the printed signed exponent. -/
namespace V8CapacityUnified.U7
open scoped Classical BigOperators

noncomputable section
set_option linter.unusedSectionVars false

theorem Cut.delta_le {m : ℕ} (c : Cut m) : c.delta≤m := by
  have hrow : c.pa.card≤m := by simpa using Finset.card_le_univ c.pa
  have hcol : c.pb.card≤m := by simpa using Finset.card_le_univ c.pb
  unfold Cut.delta
  omega

theorem signed_factor {m : ℕ} (c : Cut m) :
    (2:ℚ)^(m-c.delta+c.hazard)/2^m = (2:ℚ)^((c.hazard:ℤ)-(c.delta:ℤ)) := by
  have ht : (((m-c.delta+c.hazard:ℕ):ℤ)-(m:ℤ))=(c.hazard:ℤ)-(c.delta:ℤ) := by
    have h := c.delta_le
    omega
  rw [← ht,zpow_sub₀ (by norm_num : (2:ℚ)≠0)]
  simp only [zpow_natCast]

variable {O K B : Type*} [CommRing O] [IsDomain O] [IsLocalRing O]
variable [Field K] [Algebra O K] [IsFractionRing O K] [Fintype B]

theorem U7_printed {m : ℕ} (π : O) (hz : IsLocalRing.residue O π=0)
    (cuts : B → Cut m) (raw : B → Bits m → Bits m → K) (H : B → ℕ)
    (correct : CorrectBlocks π raw) (caps : FiberCaps π cuts raw H) :
    (1:ℚ)≤∑ b, min 1
      ((2:ℚ)^(((cuts b).hazard:ℤ)-((cuts b).delta:ℤ))*(H b:ℚ)) := by
  apply (U7_normalized π hz cuts raw H correct caps).trans_eq
  refine Finset.sum_congr rfl (fun b _ => congrArg (min 1) ?_)
  calc
    _ = ((2:ℚ)^(m-(cuts b).delta+(cuts b).hazard)/2^m) * (H b:ℚ) := by ring
    _ = _ := by rw [signed_factor]

#print axioms Cut.delta_le
#print axioms signed_factor
#print axioms U7_printed
end
end V8CapacityUnified.U7
