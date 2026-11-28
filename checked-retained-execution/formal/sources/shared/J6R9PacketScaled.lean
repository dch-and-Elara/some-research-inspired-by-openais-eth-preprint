import J6R9PacketReceive
import Mathlib.Tactic

/-! Explicit normalized crossing coefficient for the grouped child
interface. Divisibility by 2^(b+1) is not treated as an invertibility
claim; the scaled coefficient is formed by smaller nonnegative powers. -/
namespace J6R9PacketScaled
open scoped Polynomial
open J6R9PacketCoeff J6R9PacketReceive
variable {R : Type*} [CommRing R]

noncomputable def normalized {t : ℤ} {x tile i : ℕ} (a p : ℕ)
    (hnil : (2:R)^p=0) (hi : i≤a) (d : Crossing t x tile i) (z : R) (b : ℕ) : R :=
  ((2:R)^(a-d.level)*z*(cHat a t).eval₂ (J6ZeroTransport.reduceAt p hnil) z *
    inverseB a p hnil hi d z) *
    ((2:R)^(i-d.level)*inverseB a p hnil hi d z)^b

/-- This is the exact normalized factorization required by the
child profile, including when the printed power is zero in the ring. -/
theorem normalized_exact {t : ℤ} {x tile i : ℕ} (a p : ℕ)
    (hnil : (2:R)^p=0) (hi : i≤a) (d : Crossing t x tile i) (z : R) (b : ℕ) :
    mode a p hnil hi d z b = (2:R)^(b+1)*normalized a p hnil hi d z b := by
  have hd := d.level_le
  have ha : a+1-d.level = (a-d.level)+1 := by omega
  have hb : i+1-d.level = (i-d.level)+1 := by omega
  unfold mode leading ratio normalized
  rw [ha,hb,pow_succ,pow_succ,pow_succ]
  have hm : (2:R)^(i-d.level)*2*inverseB a p hnil hi d z =
      (2:R)*((2:R)^(i-d.level)*inverseB a p hnil hi d z) := by ring
  rw [hm,mul_pow]
  ring

#print axioms normalized_exact
end J6R9PacketScaled
