import Mathlib.Data.ZMod.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

namespace Reconstruction.ColorAlphabet

abbrev Colors (k : ℕ) := ZMod (2 * k + 1)

def InInterval {k : ℕ} (start c : Colors k) : Prop :=
  (c - start).val < k

instance {k : ℕ} (s : Colors k) : DecidablePred (InInterval s) :=
  fun _ => inferInstanceAs (Decidable (_ < _))

/-- For the matching numbered j these are the colors on the two boundaries
of the interval of length k containing zero. -/
def leftColor {k : ℕ} (j : Fin k) : Colors k := (k + 1 + j.val : ℕ)

def rightColor {k : ℕ} (j : Fin k) : Colors k := (j.val + 1 : ℕ)

def matchingStart {k : ℕ} (j : Fin k) : Colors k := rightColor j - (k : ℕ)

theorem leftColor_val {k : ℕ} (j : Fin k) : (leftColor j).val = k + 1 + j.val :=
  ZMod.val_natCast_of_lt (by have := j.isLt; omega)

theorem rightColor_val {k : ℕ} (j : Fin k) : (rightColor j).val = j.val + 1 :=
  ZMod.val_natCast_of_lt (by have := j.isLt; omega)

theorem matchingStart_injective {k : ℕ} : Function.Injective (@matchingStart k) := by
  intro i j h
  have h' := congrArg (fun s : Colors k => (s + (k : ℕ)).val) h
  simp only [matchingStart, sub_add_cancel, rightColor_val] at h'
  exact Fin.ext (by omega)

theorem zero_in_matchingInterval {k : ℕ} (j : Fin k) :
    InInterval (matchingStart j) 0 := by
  have h : (0 : Colors k) - matchingStart j = ((k - (j.val + 1) : ℕ) : Colors k) := by
    rw [matchingStart, rightColor, Nat.cast_sub (by have := j.isLt; omega)]
    ring
  rw [InInterval, h, ZMod.val_natCast_of_lt (by omega)]
  have := j.isLt
  omega

theorem omitted_boundaries_force_start {k : ℕ} (j : Fin k) (s : Colors k)
    (hl : ¬ InInterval s (leftColor j)) (hr : ¬ InInterval s (rightColor j)) :
    s = matchingStart j := by
  have hk := j.isLt
  have hright : rightColor j - s = (matchingStart j - s) + (k : ℕ) := by
    rw [matchingStart]
    ring
  have hleft : leftColor j - s = (matchingStart j - s) + (2 * k : ℕ) := by
    unfold leftColor matchingStart rightColor
    push_cast
    ring
  let d := (matchingStart j - s).val
  have hd : d < 2 * k + 1 := ZMod.val_lt _
  have hkl : ((2 * k : ℕ) : Colors k).val = 2 * k := ZMod.val_natCast_of_lt (by omega)
  have hkr : ((k : ℕ) : Colors k).val = k := ZMod.val_natCast_of_lt (by omega)
  change ¬ (leftColor j - s).val < k at hl
  change ¬ (rightColor j - s).val < k at hr
  rw [hleft, ZMod.val_add, hkl] at hl
  rw [hright, ZMod.val_add, hkr] at hr
  change ¬ (d + 2 * k) % (2 * k + 1) < k at hl
  change ¬ (d + k) % (2 * k + 1) < k at hr
  have hd0 : d = 0 := by
    by_contra! h
    have h1 : (d + 2*k) % (2*k+1) = d-1 := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    rw [h1] at hl
    have h2 : (d+k) % (2*k+1) = d-k-1 := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    rw [h2] at hr
    omega
  apply Eq.symm
  apply sub_eq_zero.mp
  exact ZMod.val_injective _ (show (matchingStart j - s).val = (0 : Colors k).val from hd0)

theorem nonzero_color_boundary {k : ℕ} (c : Colors k) (hc : c ≠ 0) :
    (∃ j : Fin k, c = leftColor j) ∨ ∃ j : Fin k, c = rightColor j := by
  have hv0 : c.val ≠ 0 := fun h => hc (ZMod.val_injective _ (by simpa using h))
  have hv := c.val_lt
  by_cases h : c.val ≤ k
  · refine Or.inr ⟨⟨c.val - 1, by omega⟩, ?_⟩
    apply ZMod.val_injective _
    rw [rightColor_val]
    dsimp
    omega
  · refine Or.inl ⟨⟨c.val - (k+1), by omega⟩, ?_⟩
    apply ZMod.val_injective _
    rw [leftColor_val]
    dsimp
    omega

theorem one_interval_card (k : ℕ) :
    Fintype.card {c : Colors k // InInterval (1 : Colors k) c} = k := by
  let e : {c : Colors k // InInterval (1 : Colors k) c} ≃ Fin k :=
    { toFun := fun c => ⟨(c.val - 1).val, c.property⟩
      invFun := fun i => ⟨(i.val : Colors k) + 1, by
        rw [InInterval, add_sub_cancel_right, ZMod.val_natCast_of_lt (by have := i.isLt; omega)]
        exact i.isLt⟩
      left_inv := by
        intro c
        apply Subtype.ext
        change (((c.val - 1).val : ℕ) : Colors k) + 1 = c.val
        rw [ZMod.natCast_zmod_val, sub_add_cancel]
      right_inv := by
        intro i
        apply Fin.ext
        change (((i.val : ℕ) : Colors k) + 1 - 1).val = i.val
        rw [add_sub_cancel_right, ZMod.val_natCast_of_lt (by have := i.isLt; omega)] }
  rw [Fintype.card_congr e, Fintype.card_fin]

theorem zero_not_mem_one_interval (k : ℕ) : ¬ InInterval (1 : Colors k) 0 := by
  have h : (0 : Colors k) - 1 = ((2 * k : ℕ) : Colors k) := by
    have hp : (((2 * k + 1 : ℕ) : Colors k)) = 0 := ZMod.natCast_self _
    push_cast at hp ⊢
    linear_combination - hp
  rw [InInterval, h, ZMod.val_natCast_of_lt (by omega)]
  omega

end Reconstruction.ColorAlphabet
