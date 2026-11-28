import LayoutMismatchPacking
import Mathlib.Data.Nat.Choose.Sum

namespace Reconstruction.LayoutMismatch
open scoped BigOperators
noncomputable section

variable {I V : Type*} [Fintype I] [DecidableEq I]

/-- The unnormalized finite positive-part binomial sum in Section 4. -/
def chooseExcess (R h : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (h + 1), h.choose i * (h - R - 2 * i)

/-- The paper's `φ_R(h)`, using natural subtraction for the positive part. -/
def phi (R h : ℕ) : ℚ := (chooseExcess R h : ℚ) / (2 : ℚ) ^ h

abbrev Active (w : Word I) := {i : I // (w i).1 ≠ (w i).2}
abbrev Inactive (w : Word I) := {i : I // ¬((w i).1 ≠ (w i).2)}

def mismatchCount (w : Word I) : ℕ := Fintype.card (Active w)

private def slotEquiv [Fintype V] [DecidableEq V] (w : V → Word I) (J : ℕ) :
    Slot w J ≃ Σ p : V × Mask I, Fin (J + 1 - weight p.2 - weight (dualMask (w p.1) p.2)) where
  toFun u := ⟨u.val.2, ⟨u.val.1.val - weight u.val.2.2, by
    have hin := u.property.1
    have hout := u.property.2
    have hj := u.val.1.isLt
    omega⟩⟩
  invFun u :=
    let j := u.2.val + weight u.1.2
    ⟨(⟨j, by have hj := u.2.isLt; dsimp [j]; omega⟩, u.1), by
      have hj := u.2.isLt
      dsimp [j]
      omega⟩
  left_inv u := by
    apply Subtype.ext
    refine Prod.ext (Fin.ext ?_) rfl
    change u.val.1.val - weight u.val.2.2 + weight u.val.2.2 = u.val.1.val
    exact Nat.sub_add_cancel u.property.1
  right_inv u := by
    refine Sigma.ext rfl (heq_of_eq (Fin.ext ?_))
    change u.2.val + weight u.1.2 - weight u.1.2 = u.2.val
    exact Nat.add_sub_cancel _ _

theorem slot_card_eq_sum [Fintype V] [DecidableEq V] (w : V → Word I) (J : ℕ) :
    Fintype.card (Slot w J) =
      ∑ v, ∑ s : Mask I, (J + 1 - weight s - weight (dualMask (w v) s)) := by
  rw [Fintype.card_congr (slotEquiv w J), Fintype.card_sigma, Fintype.sum_prod_type]
  simp

omit [DecidableEq I] in
private theorem card_parts (w : Word I) :
    Fintype.card I = Fintype.card (Active w) + Fintype.card (Inactive w) := by
  rw [← Fintype.card_sum]
  exact Fintype.card_congr (Equiv.sumCompl (fun t => (w t).1 ≠ (w t).2)).symm

private theorem weight_eq_sum {X : Type*} [Fintype X] (s : Mask X) :
    weight s = ∑ i, if s i = true then 1 else 0 := by
  rw [← Finset.sum_filter]
  simp [weight, ones]

omit [DecidableEq I] in
private theorem weight_add_dual (w : Word I) (s : Mask I) :
    weight s + weight (dualMask w s) =
      2 * weight (fun t : Active w => s t.val) + Fintype.card (Inactive w) := by
  rw [weight_eq_sum, weight_eq_sum, weight_eq_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
  rw [← (Equiv.sumCompl (fun t => (w t).1 ≠ (w t).2)).sum_comp
    (fun i => (if s i = true then 1 else 0) + (if dualMask w s i = true then 1 else 0))]
  rw [Fintype.sum_sum_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro t _
    change (if s t.val = true then 1 else 0) +
      (if dualMask w s t.val = true then 1 else 0) = 2 * (if s t.val = true then 1 else 0)
    simp only [dualMask, if_neg t.property, two_mul]
  · calc
      _ = ∑ _ : Inactive w, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro t _
        change (if s t.val = true then 1 else 0) +
          (if dualMask w s t.val = true then 1 else 0) = 1
        have ht : (w t.val).1 = (w t.val).2 := of_not_not t.property
        cases h : s t.val <;> simp [dualMask, ht, h]
      _ = _ := by simp

private def maskFinsetEquiv {X : Type*} [Fintype X] [DecidableEq X] :
    Mask X ≃ Finset X where
  toFun := ones
  invFun v := fun i => decide (i ∈ v)
  left_inv s := by
    funext i
    cases h : s i <;> simp [ones, h]
  right_inv s := by
    ext i
    simp [ones]

private theorem sum_mask_by_weight {X : Type*} [Fintype X] [DecidableEq X] (f : ℕ → ℕ) :
    (∑ s : Mask X, f (weight s)) =
      ∑ i ∈ Finset.range (Fintype.card X + 1), (Fintype.card X).choose i * f i := by
  have heq (s : Mask X) : f (weight s) = f (maskFinsetEquiv s).card := rfl
  simp only [heq]
  rw [maskFinsetEquiv.sum_comp (fun s : Finset X => f s.card)]
  have hu : (Finset.univ : Finset X).powerset = Finset.univ := by
    ext s
    simp
  simpa only [hu, Finset.card_univ, nsmul_eq_mul] using
    (Finset.sum_powerset_apply_card f (x := (Finset.univ : Finset X)))

private theorem sum_excess (w : Word I) (R : ℕ) :
    (∑ s : Mask I, (Fintype.card I - R - weight s - weight (dualMask w s))) =
      2 ^ Fintype.card (Inactive w) * chooseExcess R (mismatchCount w) := by
  have heq (s : Mask I) :
      Fintype.card I - R - weight s - weight (dualMask w s) =
        mismatchCount w - R - 2 * weight (fun t : Active w => s t.val) := by
    have hc := card_parts w
    have hs := weight_add_dual w s
    unfold mismatchCount
    omega
  simp only [heq]
  let e : Mask I ≃ Mask (Active w) × Mask (Inactive w) :=
    Equiv.piEquivPiSubtypeProd (fun t => (w t).1 ≠ (w t).2) (fun _ => Bool)
  change (∑ s : Mask I, (fun u : Mask (Active w) × Mask (Inactive w) =>
    mismatchCount w - R - 2 * weight u.1) (e s)) = _
  rw [e.sum_comp (fun u : Mask (Active w) × Mask (Inactive w) =>
    mismatchCount w - R - 2 * weight u.1), Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
    Fintype.card_bool, ← Finset.mul_sum]
  rw [sum_mask_by_weight (fun z => mismatchCount w - R - 2 * z)]
  rfl

/-- Summing over all tensor modes is exactly the normalized mismatch binomial sum. -/
theorem weightedModeSum (w : Word I) (R : ℕ) :
    ((∑ s : Mask I, (Fintype.card I - R - weight s - weight (dualMask w s)) : ℕ) : ℚ) =
      (2 : ℚ) ^ Fintype.card I * phi R (mismatchCount w) := by
  rw [sum_excess, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, phi, card_parts w, pow_add]
  unfold mismatchCount
  have hp : (2 : ℚ) ^ Fintype.card (Active w) ≠ 0 := pow_ne_zero _ (by decide)
  field_simp

private theorem cast_positive_part (h R i : ℕ) :
    ((h - R - 2 * i : ℕ) : ℚ) = max ((h : ℚ) - R - 2 * (i : ℚ)) 0 := by
  by_cases hk : R + 2 * i ≤ h
  · have hr : R ≤ h := by omega
    have hi : 2 * i ≤ h - R := by omega
    have hrat : (R : ℚ) + 2 * (i : ℚ) ≤ h := by exact_mod_cast hk
    have hnon : 0 ≤ (h : ℚ) - R - 2 * (i : ℚ) :=
      sub_nonneg.mpr ((le_sub_iff_add_le).mpr (by simpa [add_comm] using hrat))
    rw [max_eq_left hnon, Nat.cast_sub hi, Nat.cast_sub hr, Nat.cast_mul, Nat.cast_ofNat]
  · have hz : h - R - 2 * i = 0 := by omega
    have hrat : (h : ℚ) ≤ (R : ℚ) + 2 * (i : ℚ) := by
      exact_mod_cast (Nat.lt_of_not_ge hk).le
    have hnon : (h : ℚ) - R - 2 * (i : ℚ) ≤ 0 :=
      sub_nonpos.mpr ((sub_le_iff_le_add).mpr (by simpa [add_comm] using hrat))
    rw [hz, Nat.cast_zero, max_eq_right hnon]

/-- The rational positive-part expression for `φ_R(h)` printed in the paper. -/
theorem phi_eq_positive_part (R h : ℕ) :
    phi R h = ((2 : ℚ) ^ h)⁻¹ *
      ∑ i ∈ Finset.range (h + 1), (h.choose i : ℚ) * max ((h : ℚ) - R - 2 * (i : ℚ)) 0 := by
  simp only [phi, chooseExcess, Nat.cast_sum, Nat.cast_mul, cast_positive_part, div_eq_mul_inv]
  exact mul_comm _ _

end
end Reconstruction.LayoutMismatch
