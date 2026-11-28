import J6R9PacketChild
import Mathlib.Tactic

set_option warningAsError true

namespace Paper5.OuterCenters
open scoped BigOperators
open P11FullPacking J6R9PacketChild J6R9PacketScopes J6R9PacketLocal J6R9PacketScaled

/-- A central slot cannot be matched at either end of the Cauchy grid. -/
theorem outer_slot_unmatched (L K x y : ℕ) (t : ℤ)
    (hx₀ : K ≤ x) (hx₁ : x + K < L) (hy : y < L)
    (ht : (L : ℤ) - K ≤ t ∨ t ≤ -((L : ℤ) - K)) :
    (y : ℤ) - (x : ℤ) ≠ t := by
  intro h
  rcases ht with ht | ht <;> omega

variable {S A B R : Type*} [LinearOrder S] [CommRing R] [Fintype B] {a b : ℕ}

/-- The genuine normalized target coefficient, not merely its weighted
multiple, vanishes at the legal zero local probe. -/
theorem crossNorm_zero (mask : MaskFamily a b S) (i : Fin a)
    {t : ℤ} (ht : t ≠ 0) (hv : padicValInt 2 t = i.val) (p : ℕ)
    (hnil : (2 : R)^p = 0) (w : Physical a b S) (m : Mode i p mask) :
    crossNorm mask i ht hv p hnil 0 w m = 0 := by
  classical
  unfold crossNorm
  split <;> simp [normalized]

/-- For a physically unmatched port, the actual same-group column sum vanishes. -/
theorem localValue_zero_of_unmatched (κ : B → Physical a b S)
    (mask : MaskFamily a b S) (i : Fin a) (t : ℤ) (p : ℕ)
    (hnil : (2 : R)^p = 0) (w : Physical a b S)
    (X : ColBits κ mask i (rowGroup mask i w))
    (h : ∀ q : B, (κ q).1 = w.1 →
      ((κ q).2.val : ℤ) - (w.2.val : ℤ) ≠ t) :
    localValue κ mask i t p hnil 0 w X = 0 := by
  classical
  unfold localValue
  apply Finset.sum_eq_zero
  intro q _
  split
  next hq =>
    rw [W, if_neg (h q.val hq)]
    simp [Polynomial.eval₂_mul]
  next => rfl

/-- Every choice in the actual packet row (constant or normalized mode)
vanishes when the unmatched row's fixed original pin is one. -/
theorem sentry_actual_row_zero (ρ : A → Physical a b S) (κ : B → Physical a b S)
    (mask : MaskFamily a b S) (i : Fin a)
    {t : ℤ} (ht : t ≠ 0) (hv : padicValInt 2 t = i.val) (p : ℕ)
    (hnil : (2 : R)^p = 0) (r : A) (v : State ρ κ mask i (rowGroup mask i (ρ r)))
    (hpin : v.1 ⟨r, rfl⟩ = true)
    (h : ∀ q : B, (κ q).1 = (ρ r).1 →
      ((κ q).2.val : ℤ) - ((ρ r).2.val : ℤ) ≠ t) (m : Option (Mode i p mask)) :
    row ρ κ mask i ht hv p hnil 0 r v m = 0 := by
  cases m with
  | none =>
    simp [row, hpin, localValue_zero_of_unmatched κ mask i t p hnil (ρ r) v.2 h,
      LiteralPortCompiler.affine]
  | some m => simp [row, crossNorm_zero]

#print axioms outer_slot_unmatched
#print axioms crossNorm_zero
#print axioms localValue_zero_of_unmatched
#print axioms sentry_actual_row_zero

end Paper5.OuterCenters
