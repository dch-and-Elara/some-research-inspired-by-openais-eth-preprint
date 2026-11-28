import ColorAlphabetCyclic
import ColorAlphabetLower
import Mathlib.Tactic.NormNum

open scoped BigOperators
open Reconstruction.ColorAlphabet

namespace Reconstruction.ReleaseColor

noncomputable section

theorem boundary_colors_omitted_iff {k : ℕ} (j : Fin k) (s : Colors k) :
    (¬InInterval s (leftColor j) ∧ ¬InInterval s (rightColor j)) ↔ s = matchingStart j := by
  have hk := j.isLt
  constructor
  · rintro ⟨hl, hr⟩
    exact omitted_boundaries_force_start j s hl hr
  · rintro rfl
    have hleft : leftColor j - matchingStart j = ((2*k : ℕ) : Colors k) := by
      unfold leftColor matchingStart rightColor
      push_cast
      ring
    have hright : rightColor j - matchingStart j = (k : Colors k) := by simp [matchingStart]
    simp only [InInterval, hleft, hright,
      ZMod.val_natCast_of_lt (by omega : 2*k < 2*k+1),
      ZMod.val_natCast_of_lt (by omega : k < 2*k+1)]
    omega

/-- Every interval containing zero is the interval assigned to exactly one round. -/
theorem intervals_containing_zero (k : ℕ) :
    Fintype.card {s : Colors k // InInterval s 0} = k := by
  let e : {s : Colors k // InInterval s 0} ≃ Fin k :=
    { toFun := fun s => ⟨(0-s.val).val, s.property⟩
      invFun := fun j => ⟨-((j.val : ℕ) : Colors k), by
        simpa only [InInterval, zero_sub, neg_neg,
          ZMod.val_natCast_of_lt (j.isLt.trans (by omega : k < 2*k+1))] using j.isLt⟩
      left_inv := by
        intro s
        apply Subtype.ext
        change -((((0 - s.val).val : ℕ) : Colors k)) = s.val
        rw [ZMod.natCast_zmod_val, zero_sub, neg_neg]
      right_inv := by
        intro j
        apply Fin.ext
        change (0 - -((j.val : ℕ) : Colors k)).val = j.val
        simp only [zero_sub, neg_neg,
          ZMod.val_natCast_of_lt (j.isLt.trans (by omega : k < 2*k+1))] }
  rw [Fintype.card_congr e, Fintype.card_fin]

theorem matchingStart_bijective (k : ℕ) :
    Function.Bijective (fun j : Fin k =>
      (⟨matchingStart j, zero_in_matchingInterval j⟩ : {s : Colors k // InInterval s 0})) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨fun i j h => matchingStart_injective (congrArg Subtype.val h),
    (Fintype.card_fin k).trans (intervals_containing_zero k).symm⟩

/-- The bracketed two-step exchange appearing in the Proposition 2.1 proof. -/
theorem receiver_exchange_identity (x y : ℚ) :
    (x-1)*y^2 + (y-1)*(x-1)^2 - (y-1)*x^2 - (x-1)*(y-1)^2 = x-y := by ring

theorem binary_paper_endpoint_values :
    uniformConverse 2 2 = 5 ∧ uniformConverse 3 2 = 21 ∧
      (2 : ℕ) + (2+1)/2+2 = 5 ∧ (3 : ℕ) + (3+1)/2+2 = 7 := by
  rw [binary_converse_value, binary_converse_value]
  norm_num

end
end Reconstruction.ReleaseColor
