import J6R22ActiveScaledSum
import J6R18ChildWriteKernel

/-! Exact modular formula for the common-cleared source Hermite
weight. The amount shifted is derived from the actual numerator
and denominator factors, and cannot use truncated subtraction
unless the printed loss estimate makes the shift nonnegative. -/
namespace J6R23ScheduleWeight
open scoped Polynomial
open P1DyadicGrid P1DyadicGridBridge HermiteLoss DenominatorBudget
open AOracleSuccinctNative J6R22Active J6R18ChildWrite

theorem weightNum_nonzero (a u h j : ℕ) {t : ℤ} (ht : t≠0) :
    weightNum a u h j t≠0 :=
  mul_ne_zero (numerator_ne a u h t) (pow_ne_zero _ (neg_ne_zero.mpr ht))

theorem weightDen_nonzero (a u h j : ℕ) (t : ℤ) :
    weightDen a u h j t≠0 :=
  mul_ne_zero (denominator_ne a u h t) (pow_ne_zero _ (pow₂_pos _).ne')

theorem weight_real_shift_nonnegative (a u h j : ℕ) {t : ℤ} (ht : t∈grid a)
    (hn : t≠0) {B : ℕ} (hB : totalLoss a h j t≤B) :
    level (weightDen a u h j t)≤B+level (weightNum a u h j t) := by
  have hh := denominator_loss_le a u h ht hn
  have hN : level (weightNum a u h j t)=level (numerator a u h t)+j*level t := by
    unfold weightNum
    rw [show level (numerator a u h t*(-t)^j)=level (numerator a u h t)+level ((-t)^j) from
      padicValInt.mul (numerator_ne a u h t) (pow_ne_zero _ (neg_ne_zero.mpr hn)),
      level_power (neg_ne_zero.mpr hn),level_neg]
  have hD : level (weightDen a u h j t)=level (denominator a u h t)+j*(a+1) := by
    unfold weightDen
    rw [show level (denominator a u h t*pow₂ (a+1)^j)=level (denominator a u h t)+level (pow₂ (a+1)^j) from
      padicValInt.mul (denominator_ne a u h t) (pow_ne_zero _ (pow₂_pos _).ne'),
      level_power (pow₂_pos _).ne',level_pow₂]
  have hsum : j*(a+1)=j*(a+1-level t)+j*level t := by
    rw [←Nat.mul_add,Nat.sub_add_cancel ((level_grid_le ht hn).trans (Nat.le_succ _))]
  rw [hN,hD,hsum]
  unfold totalLoss at hB
  omega

theorem scaled_weight_rational_parts (a u h B j : ℕ) {t : ℤ}
    (ht : t∈grid a) (hn : t≠0) (hB : totalLoss a h j t≤B) :
    let N := weightNum a u h j t
    let D := weightDen a u h j t
    let e := B+level N-level D
    twoLocalRat (scaledWeight a u h B j t)=
      ((pow₂ e*oddWord N:ℤ):ℚ)/(oddWord D:ℚ) := by
  let N := weightNum a u h j t
  let D := weightDen a u h j t
  let e := B+level N-level D
  have fit := weight_real_shift_nonnegative a u h j ht hn hB
  have hs : B+level N=e+level D := (Nat.sub_add_cancel fit).symm
  obtain ⟨_,hN⟩ := oddWord_factor (weightNum_nonzero a u h j hn)
  obtain ⟨od,hD⟩ := oddWord_factor (weightDen_nonzero a u h j t)
  have hrN : (N:ℚ)=(2:ℚ)^level N*(oddWord N:ℚ) := by
    simpa only [Int.cast_mul,int_power_rat] using congrArg (fun x : ℤ=>(x:ℚ)) hN
  have hrD : (D:ℚ)=(2:ℚ)^level D*(oddWord D:ℚ) := by
    simpa only [Int.cast_mul,int_power_rat] using congrArg (fun x : ℤ=>(x:ℚ)) hD
  have oddNe : (oddWord D:ℚ)≠0 := by exact_mod_cast odd_int_ne_zero od
  dsimp only
  rw [scaled_weight_read ht hn hB]
  change (2:ℚ)^B*((N:ℚ)/(D:ℚ))=((pow₂ e*oddWord N:ℤ):ℚ)/(oddWord D:ℚ)
  rw [hrN,hrD,Int.cast_mul,int_power_rat]
  calc
    _ = ((2:ℚ)^(B+level N)*(oddWord N:ℚ))/((2:ℚ)^level D*(oddWord D:ℚ)) := by
      rw [pow_add]
      ring
    _ = _ := by
      rw [hs,pow_add]
      field_simp

theorem scaled_word_formula {R : Type*} [CommRing R] (p : ℕ) (nil : (2:R)^p=0)
    (a u h B j : ℕ) {t : ℤ} (ht : t∈grid a) (hn : t≠0) (hB : totalLoss a h j t≤B) :
    let N := weightNum a u h j t
    let D := weightDen a u h j t
    let e := B+level N-level D
    J6ZeroTransport.reduceAt p nil (scaledWeight a u h B j t)=
      (2:R)^e*(oddWord N:R)*oddInverse p (oddWord D:R) := by
  let N := weightNum a u h j t
  let D := weightDen a u h j t
  let e := B+level N-level D
  have hO := (oddWord_factor (weightDen_nonzero a u h j t)).1
  have no2 : ¬ (2:ℤ)∣oddWord D := fun H=>
    (Int.not_even_iff_odd.mpr hO) (even_iff_two_dvd.mpr H)
  have hQ := scaled_weight_rational_parts a u h B j ht hn hB
  change J6ZeroTransport.reduceAt p nil (scaledWeight a u h B j t)=_
  rw [J6ZeroTransport.reduce_fraction p nil _ (pow₂ e*oddWord N) (oddWord D) no2 hQ,
    odd_reciprocal_same p nil _ hO,Int.cast_mul]
  simp only [pow₂,Int.cast_pow,Int.cast_ofNat]
  rfl

#print axioms weight_real_shift_nonnegative
#print axioms scaled_weight_rational_parts
#print axioms scaled_word_formula
end J6R23ScheduleWeight


