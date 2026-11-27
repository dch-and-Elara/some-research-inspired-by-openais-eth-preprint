import SharpFactor
import OppositeRows
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace SharpFactor

open Matrix Polynomial

/-- The unnormalized square submatrix in SHARP.md, step 2. -/
noncomputable def halfSampleMatrix {k : ℕ} (e : Fin k → ℕ) : Matrix (Fin k) (Fin k) ℚ[X] :=
  Matrix.of fun i j => (1 + C (2 * (i.val : ℚ)) * X) ^ e j

/-- The unordered row pairs selected by a positive sum s, with smaller index first. -/
abbrev SumPairs (k s : ℕ) :=
  {ij : Fin k × Fin k // ij.1 < ij.2 ∧ ij.1.val + ij.2.val = s}

noncomputable instance (k s : ℕ) : Fintype (SumPairs k s) := Fintype.ofFinite _

/-- The individual rational factor of the raw determinant, with exactly the
pair count and the smaller parity count appearing in SHARP.md, step 2. -/
theorem halfSample_factor {k s : ℕ} (hs : 0 < s) (e : Fin k → ℕ) :
    (1 + C (s : ℚ) * X) ^
        (Fintype.card (SumPairs k s) -
          min (Fintype.card {j // Even (e j)}) (Fintype.card {j // Odd (e j)})) ∣
      (halfSampleMatrix e).det := by
  classical
  let l : SumPairs k s ↪ Fin k :=
    ⟨fun i => i.1.1, fun a b h => by
      apply Subtype.ext
      apply Prod.ext
      · exact h
      · apply Fin.ext
        have ha := a.2.2
        have hb := b.2.2
        have h₁ := congrArg Fin.val h
        change a.val.1.val = b.val.1.val at h₁
        omega⟩
  let r : SumPairs k s ↪ Fin k :=
    ⟨fun i => i.1.2, fun a b h => by
      apply Subtype.ext
      apply Prod.ext
      · apply Fin.ext
        have ha := a.2.2
        have hb := b.2.2
        have h₂ := congrArg Fin.val h
        change a.val.2.val = b.val.2.val at h₂
        omega
      · exact h⟩
  have hdisj (a b : SumPairs k s) : l a ≠ r b := by
    intro h
    have h₁ := congrArg Fin.val h
    have ha := a.2
    have hb := b.2
    change a.val.1.val = b.val.2.val at h₁
    omega
  let c : ℚ := -((s : ℚ)⁻¹)
  let x : Fin k → ℚ := fun i => 1 + 2 * (i.val : ℚ) * c
  have hs0 : (s : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  have hsc : (s : ℚ) * c = -1 := by
    dsimp [c]
    rw [mul_neg, mul_inv_cancel₀ hs0]
  have hx (a : SumPairs k s) : x (r a) = -x (l a) := by
    have hsum : ((l a).val : ℚ) + ((r a).val : ℚ) = s := by
      exact_mod_cast a.2.2
    apply eq_neg_of_add_eq_zero_left
    calc
      x (r a) + x (l a) = 2 + 2 * (((l a).val : ℚ) + ((r a).val : ℚ)) * c := by
        simp only [x]
        ring
      _ = 0 := by rw [hsum, mul_assoc, hsc]; norm_num
  let d := Fintype.card (SumPairs k s) -
    min (Fintype.card {j // Even (e j)}) (Fintype.card {j // Odd (e j)})
  change (1 + C (s : ℚ) * X) ^ d ∣ _
  have hr := opposite_powers_rank_deficiency x e l r hdisj hx
  have heval : (halfSampleMatrix e).map (Polynomial.evalRingHom c) =
      Matrix.of (fun (i j : Fin k) => x i ^ e j) := by
    ext i j
    simp [halfSampleMatrix, x]
  rw [← heval] at hr
  have hbound := (halfSampleMatrix e).map (Polynomial.evalRingHom c) |>.rank_le_card_width
  have hdiv : (X - C c)^d ∣ (halfSampleMatrix e).det := by
    apply pow_X_sub_C_dvd_det_of_rank
    change d ≤ _ at hr
    omega
  have hshape : 1 + C (s : ℚ) * X = C (s : ℚ) * (X - C c) := by
    rw [mul_sub, ← map_mul, hsc, map_neg, map_one, sub_neg_eq_add, add_comm]
  rw [hshape, mul_pow]
  have hunit : IsUnit (C (s : ℚ)^d) := ((isUnit_iff_ne_zero.mpr hs0).map Polynomial.C).pow d
  have hone : C (s : ℚ)^d ∣ 1 := hunit.dvd
  simpa only [one_mul] using mul_dvd_mul hone hdiv

end SharpFactor
