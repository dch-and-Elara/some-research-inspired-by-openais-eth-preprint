import J6R16SpecializedBoxSelected
import J6R16SpecializedBoxBounds

/-! The displayed J7 precision inequality follows from the inherited
printed child precision at the actual odd extreme, without a rounding
loss. It is distinct from the convenient 10M-bit integer-fit threshold. -/
namespace J7R43Literal
open J6ActiveSchedule J6R14SpecializedBox P1DyadicGrid
set_option autoImplicit false

theorem literal_J7_precision_lower (p a M u : ℕ) (ha : 0<a)
    (hu : 0<u) (huM : u≤M) :
    24*M*2^a ≤ childPrecision p a M u (((2^a:ℕ):ℤ)-1)*u := by
  have ht := odd_valuation_zero (positiveExtreme_odd a ha)
  have hk : 8*height M u*(2^a) ≤ childPrecision p a M u (((2^a:ℕ):ℤ)-1) := by
    rw [childPrecision,ht,pow_zero,Nat.div_one]
    unfold J9PrintedSchedule.precision
    omega
  calc
    _ = (3*M)*(8*2^a) := by ring
    _ ≤ (height M u*u)*(8*2^a) := Nat.mul_le_mul_right _ (height_bounds M u hu huM).1
    _ = (8*height M u*2^a)*u := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hk

#print axioms literal_J7_precision_lower
end J7R43Literal