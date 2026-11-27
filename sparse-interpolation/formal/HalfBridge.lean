import Threshold
import GrenetHalf

open GrenetHalf Round4Transfer

namespace GrenetRational

theorem den_le_two_iff_double_integer (z : ℚ) :
    z.den ≤ 2 ↔ ∃ c : ℤ, 2*z = (c : ℚ) := by
  constructor
  · intro h
    have hp := z.den_pos
    have he := z.num_div_den
    rcases (show z.den = 1 ∨ z.den = 2 by omega) with hd | hd
    · refine ⟨2*z.num, ?_⟩
      rw [hd, Nat.cast_one, div_one] at he
      rw [Int.cast_mul, Int.cast_ofNat]
      exact congrArg (fun q : ℚ => 2*q) he.symm
    · refine ⟨z.num, ?_⟩
      rw [hd, Nat.cast_ofNat] at he
      calc
        2*z = 2*((z.num : ℚ)/2) := congrArg (fun r => 2*r) he.symm
        _ = z.num := by ring
  · rintro ⟨c, hc⟩
    have hz : z = Rat.divInt c 2 := by
      rw [Rat.divInt_eq_div]
      push_cast
      linarith
    have h := Rat.den_dvd c 2
    rw [← hz] at h
    exact_mod_cast Int.le_of_dvd (by decide : (0 : ℤ) < 2) h

theorem negIndices_card (z : ℚ) (m : ℕ) :
    (negIndices (normalizedPrefix z m)).card = min m (negativeLength z) := by
  let s := negIndices (normalizedPrefix z m)
  have h (i : Fin m) : i ∈ s ↔ i.val < negativeLength z := by
    change i ∈ negIndices (normalizedPrefix z m) ↔ _
    simp only [negIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact node_neg_iff z i.val
  let e : s ≃ Fin (min m (negativeLength z)) :=
    { toFun := fun i => ⟨i.val.val, lt_min_iff.mpr ⟨i.val.isLt, (h i.val).mp i.property⟩⟩
      invFun := fun i => ⟨Fin.castLE (min_le_left _ _) i, (h _).mpr (i.isLt.trans_le (min_le_right _ _))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa [s] using Fintype.card_congr e

theorem posIndices_card (z : ℚ) (m : ℕ) :
    (posIndices (normalizedPrefix z m)).card = m - firstPositive z := by
  let s := posIndices (normalizedPrefix z m)
  let p := firstPositive z
  have h (i : Fin m) : i ∈ s ↔ p ≤ i.val := by
    change i ∈ posIndices (normalizedPrefix z m) ↔ _
    simp only [posIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact node_pos_iff z i.val
  let e : s ≃ Fin (m-p) :=
    { toFun := fun i => ⟨i.val.val-p, by
        have hi := i.val.isLt
        have hp := (h i.val).mp i.property
        omega⟩
      invFun := fun i =>
        have hi := i.isLt
        ⟨⟨p+i.val, by omega⟩, (h _).mpr (by dsimp; omega)⟩
      left_inv := fun i => by
        have hp := (h i.val).mp i.property
        apply Subtype.ext
        apply Fin.ext
        change p+(i.val.val-p) = i.val.val
        omega
      right_inv := fun i => by
        apply Fin.ext
        change p+i.val-p = i.val
        omega }
  simpa [s, p] using Fintype.card_congr e

theorem half_prefix_exact (z : ℚ) (hz : z.den ≤ 2) (t m : ℕ) (ht : 1 ≤ t) :
    DeterminesUnboundedSparse (normalizedPrefix z m) t ↔ signThreshold z (2*t) ≤ m := by
  obtain ⟨c, hc⟩ := (den_le_two_iff_double_integer z).mp hz
  have hc' : 2*(z/1) = (c : ℚ) := by simpa using hc
  have h := rational_half_prefix_iff z 1 one_ne_zero c hc' m t
  change DeterminesUnboundedSparse (progression (fun i : Fin m => i.val) z 1) t ↔ _ at h
  have hnodes :
      progression (fun i : Fin m => i.val) z 1 = normalizedPrefix z m := by
    funext i
    simp [progression, normalizedPrefix, normalizedNode]
  rw [hnodes, posIndices_card, negIndices_card] at h
  rw [h, signThreshold_le_iff]
  omega

theorem half_obstruction : HalfObstructionStatement := by
  intro z hz t m ht hm h
  exact (not_le_of_gt hm) ((half_prefix_exact z hz t m ht).mp h)

end GrenetRational
