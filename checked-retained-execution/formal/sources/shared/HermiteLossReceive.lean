import HermiteLossDenominator
import HermiteLossReceiveCore

/-! The precise 2-local extrapolation multiplier and its receiving
precision. All statements are coordinatewise and so apply to every
coefficient of the source’s K[V]/(V^ell) vector. -/
namespace HermiteLoss
open P1DyadicGrid DenominatorBudget
open scoped BigOperators

def weightNum (a u h j : ℕ) (t : ℤ) : ℤ := numerator a u h t*(-t)^j

def weightDen (a u h j : ℕ) (t : ℤ) : ℤ := denominator a u h t*pow₂ (a+1)^j

noncomputable def weight (a u h j : ℕ) (t : ℤ) : ℚ :=
  (weightNum a u h j t:ℚ)/(weightDen a u h j t:ℚ)

def totalLoss (a h j : ℕ) (t : ℤ) : ℕ :=
  6*h*2^(a-level t)+j*(a+1-level t)

theorem level_neg (x : ℤ) : level (-x)=level x := by simp [level,padicValInt]

theorem weight_scaled_integral (a u h j : ℕ) {t : ℤ} (ht : t∈grid a) (h0 : t≠0) :
    (2:ℚ)^totalLoss a h j t*weight a u h j t ∈ twoLocalSubalgebra := by
  have hn := numerator_ne a u h t
  have hd := denominator_ne a u h t
  have hnot := neg_ne_zero.mpr h0
  have hpow := (pow₂_pos (a+1)).ne'
  have hvn : level (weightNum a u h j t) =
        level (numerator a u h t)+j*level t := by
    unfold weightNum
    rw [show level (numerator a u h t*(-t)^j)=
      level (numerator a u h t)+level ((-t)^j) from
      padicValInt.mul hn (pow_ne_zero _ hnot), level_power hnot,level_neg]
  have hvd : level (weightDen a u h j t) =
        level (denominator a u h t)+j*(a+1) := by
    unfold weightDen
    rw [show level (denominator a u h t*pow₂ (a+1)^j)=
      level (denominator a u h t)+level (pow₂ (a+1)^j) from
      padicValInt.mul hd (pow_ne_zero _ hpow), level_power hpow,level_pow₂]
  unfold weight
  apply scaled_ratio_integral _ _ (mul_ne_zero hn (pow_ne_zero _ hnot))
    (mul_ne_zero hd (pow_ne_zero _ hpow))
  change level (weightDen a u h j t) ≤ totalLoss a h j t + level (weightNum a u h j t)
  rw [hvn,hvd]
  have hi := level_grid_le ht h0
  have hl := denominator_loss_le a u h ht h0
  have hj : j*(a+1) = j*(a+1-level t)+j*level t := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (hi.trans (Nat.le_succ _))]
  unfold totalLoss
  rw [hj]
  omega

theorem printed_weight_precision {p M a u j : ℕ} {t : ℤ} (ht : t∈grid a) (h0 : t≠0)
    (hM : u≤M) (hj : j<taper u (sourceH M u) (level t)) {x y : ℚ}
    (data : congruence (J9PrintedSchedule.precision p (sourceH M u) (2^(a-level t)) M a) x y) :
    congruence p (weight a u (sourceH M u) j t*x) (weight a u (sourceH M u) j t*y) :=
  weight_precision_transfer (weight_scaled_integral a u (sourceH M u) j ht h0)
    (by simpa only [totalLoss,Nat.add_assoc] using
      source_loss_fits p M a (level t) u j (2^(a-level t)) hM hj) data

#print axioms weight_scaled_integral
#print axioms printed_weight_precision
end HermiteLoss

