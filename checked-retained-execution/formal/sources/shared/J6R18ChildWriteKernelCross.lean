import J6R18ChildWriteKernel
import J6R10RowIdentity

/-! The A1 crossing multiplier is the scaled physical mode value
(its factor of 2^(b+1) is already present), not the normalized row
cell before weighting. Compare two genuine unit inverses. -/
namespace J6R18ChildWrite
open scoped BigOperators Polynomial
open Polynomial DenominatorBudget P1DyadicGrid P1DyadicGridBridge
open AOracleSuccinctNative AOracleSuccinctKernel AOracleSuccinctPhysical
open J6R9PacketCoeff J6R9PacketReceive J6R9PacketScopes J6R9PacketChild J6R10RowIdentity
open P11FullPacking

variable {R : Type*} [CommRing R]

theorem crossing_oddPart {t : ℤ} {x τ i : ℕ} (d : Crossing t x τ i) :
    oddWord (crossingInt t x τ)=d.oddPart := by
  unfold oddWord
  rw [← d.val_eq]
  conv_lhs => rw [d.exact_int]
  exact Int.mul_ediv_cancel_left _ (pow₂_pos _).ne'

theorem crossing_power_eq {a i h : ℕ} (b : ℕ) (hi : i ≤ a) (hh : h ≤ i) :
    a+1-h+(i+1-h)*b=crossingExponent a i b h := by
  have hA : a+1-h=(a+1-i)+(i-h) := by omega
  have hI : i+1-h=(i-h)+1 := by omega
  rw [hA,hI,crossingExponent]
  ring

theorem mode_is_crossCell (p : ℕ) (hnil : (2:R)^p=0) {a i x τ : ℕ} {t : ℤ}
    (ht : t∈grid a) (hi : i≤a) (d : Crossing t x τ i) (z : R) (b : ℕ) :
    J6R9PacketReceive.mode a p hnil hi d z b=crossCell p a i b t x τ z := by
  let H := d.level
  let D := B a H d.oddPart z
  have ha : 0<a+1-H := by have := d.level_le; unfold H; omega
  have hInv : inverseB a p hnil hi d z=oddInverse p D := by
    apply inverse_unique (denominator_inverse_product a p hnil hi d z)
    exact inverse_shift p (a+1-H) hnil ha _ d.odd z
  unfold J6R9PacketReceive.mode leading ratio
  rw [hInv,cHat_read p hnil ht,mul_pow,← pow_mul]
  unfold crossCell
  dsimp only
  rw [← d.val_eq,crossing_oddPart d,← crossing_power_eq b hi d.level_le,pow_add]
  change (2:R)^(a+1-H)*z*(((oddPartsAt a t:R)*oddInverse p (oddDerivative a:R))*
        ∏ q∈(grid a).erase t,ratioFactor p a t q z)*oddInverse p D*
      ((2:R)^((i+1-H)*b)*oddInverse p D^b)=_
  unfold D ratioFactor B shiftWord H
  rw [pow_succ]
  ring

theorem scaled_on_target_is_crossCell {G : Type*} [LinearOrder G] {a pages : ℕ}
    (mask : MaskFamily a pages G) (i : Fin a) {t : ℤ} (htM : t∈grid a) (ht : t≠0)
    (hv : padicValInt 2 t=i.val) (p : ℕ) (hnil : (2:R)^p=0) (z : R)
    (w : Physical a pages G) (m : Mode i p mask)
    (h : rowBlock mask i w=target mask i m) :
    scaledRow mask i ht hv p hnil z w m =
      crossCell p a i.val m.order.val t w.2.val m.tile.val z := by
  unfold scaledRow
  rw [on_target_exact mask i ht hv p hnil z w m h]
  exact mode_is_crossCell p hnil htM i.isLt.le _ z _

theorem scaled_off_target_zero {G : Type*} [LinearOrder G] {a pages : ℕ}
    (mask : MaskFamily a pages G) (i : Fin a) {t : ℤ} (ht : t≠0)
    (hv : padicValInt 2 t=i.val) (p : ℕ) (hnil : (2:R)^p=0) (z : R)
    (w : Physical a pages G) (m : Mode i p mask)
    (h : rowBlock mask i w≠target mask i m) :
    scaledRow mask i ht hv p hnil z w m=0 := by
  simp [scaledRow,off_target mask i ht hv p hnil z w m h]

#print axioms crossing_power_eq
#print axioms mode_is_crossCell
#print axioms scaled_on_target_is_crossCell
#print axioms scaled_off_target_zero
end J6R18ChildWrite

