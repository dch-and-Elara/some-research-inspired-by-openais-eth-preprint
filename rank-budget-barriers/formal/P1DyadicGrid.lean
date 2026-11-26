import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic

/-!
# Integer coordinates of the Appendix D dyadic grid

The actual source grid is [-2^a,2^a). Positions within a packet, in
contrast, are nonnegative naturals. The test below translates between
their literal bit labels and the valuation of the crossing denominator.
It covers signed grid nodes, including the left endpoint.
-/

open scoped BigOperators

namespace P1DyadicGrid

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

def pow₂ (e : ℕ) : ℤ := (2:ℤ)^e

theorem pow₂_pos (e : ℕ) : 0 < pow₂ e := by unfold pow₂; positivity

theorem pow₂_succ (e : ℕ) : pow₂ (e+1) = pow₂ e * 2 := by simp [pow₂, pow_succ]

/-- Literal printed grid, including the negative endpoint and excluding
the positive endpoint. -/
def grid (a : ℕ) : Finset ℤ := Finset.Ico (-pow₂ a) (pow₂ a)

theorem mem_grid {a : ℕ} {t : ℤ} : t ∈ grid a ↔ -pow₂ a ≤ t ∧ t < pow₂ a :=
  Finset.mem_Ico

theorem zero_mem_grid (a : ℕ) : 0 ∈ grid a := by
  rw [mem_grid]
  have h := pow₂_pos a
  omega

theorem small_dvd_zero {B d : ℤ} (hlo : -B < d) (hhi : d < B)
    (hd : B ∣ d) : d = 0 := by
  by_cases h : 0 ≤ d
  · exact Int.eq_zero_of_dvd_of_nonneg_of_lt h hhi hd
  · have he := Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega : 0 ≤ -d)
      (by omega : -d < B) (Int.dvd_neg.mpr hd)
    omega

theorem grid_difference_bounds {a : ℕ} {t q : ℤ}
    (ht : t ∈ grid a) (hq : q ∈ grid a) :
    -pow₂ (a+1) < t-q ∧ t-q < pow₂ (a+1) := by
  rw [mem_grid] at ht hq
  rw [pow₂_succ]
  omega

/-- Every nonzero difference occurring in the actual product has
dyadic valuation at most a. -/
theorem grid_difference_valuation_le {a : ℕ} {t q : ℤ}
    (ht : t ∈ grid a) (hq : q ∈ grid a) (hne : t ≠ q) :
    padicValInt 2 (t-q) ≤ a := by
  have hb := grid_difference_bounds ht hq
  by_contra hh
  have he : pow₂ (a+1) ∣ t-q := by
    exact (padicValInt_dvd_iff (p := 2) (a+1) (t-q)).mpr (Or.inr (by omega))
  exact hne (sub_eq_zero.mp (small_dvd_zero hb.1 hb.2 he))

/-- Nonzero signed integer with its exact dyadic factor and an odd
unit. The odd factor can be negative. -/
theorem integer_odd_factor {d : ℤ} (hd : d ≠ 0) :
    ∃ w : ℤ, Odd w ∧ d = pow₂ (padicValInt 2 d) * w := by
  have hdiv : pow₂ (padicValInt 2 d) ∣ d := padicValInt_dvd (p := 2) d
  obtain ⟨w, hw⟩ := hdiv
  refine ⟨w, Int.not_even_iff_odd.mp (fun hEven => ?_), hw⟩
  obtain ⟨k, hk⟩ := even_iff_two_dvd.mp hEven
  have hbad : pow₂ (padicValInt 2 d + 1) ∣ d := by
    refine ⟨k, ?_⟩
    calc
      d = pow₂ (padicValInt 2 d)*w := hw
      _ = pow₂ (padicValInt 2 d+1)*k := by rw [hk, pow₂_succ, mul_assoc]
  have hx := (padicValInt_dvd_iff (p := 2) (padicValInt 2 d+1) d).mp hbad
  rcases hx with h | h
  · exact hd h
  · omega

theorem odd_int_ne_zero {w : ℤ} (hw : Odd w) : w ≠ 0 := by
  exact fun h => (Int.not_even_iff_odd.mpr (h ▸ hw)) (show Even (0:ℤ) from ⟨0, by simp⟩)

theorem odd_valuation_zero {w : ℤ} (hw : Odd w) : padicValInt 2 w = 0 :=
  padicValInt.eq_zero_of_not_dvd
    (fun h => (Int.not_even_iff_odd.mpr hw) (even_iff_two_dvd.mpr h))

/-- A node specified by its signed odd multiplier is literally at level i. -/
theorem valuation_pow₂_mul_odd (i : ℕ) {w : ℤ} (hw : Odd w) :
    padicValInt 2 (pow₂ i * w) = i := by
  induction i with
  | zero => simpa [pow₂] using odd_valuation_zero hw
  | succ i ih =>
    have hn : pow₂ i * w ≠ 0 := mul_ne_zero (ne_of_gt (pow₂_pos i)) (odd_int_ne_zero hw)
    have h : pow₂ (i+1) * w = (pow₂ i * w)*2 := by
      rw [pow₂_succ]; ring
    rw [h]
    exact (padicValInt_mul_eq_succ (p := 2) _ hn).trans (congrArg (·+1) ih)

theorem level_iff_odd_multiplier {t : ℤ} (ht : t ≠ 0) (i : ℕ) :
    padicValInt 2 t = i ↔ ∃ w : ℤ, Odd w ∧ t = pow₂ i * w := by
  constructor
  · intro h
    simpa only [h] using integer_odd_factor ht
  · rintro ⟨w, hw, rfl⟩
    exact valuation_pow₂_mul_odd i hw

/-- In the residue ring for a tile, every signed integer of exact level i
has precisely the half-period residue. -/
theorem level_modEq_half {t : ℤ} {i : ℕ} (ht : t ≠ 0) (hi : padicValInt 2 t = i) :
    t ≡ pow₂ i [ZMOD pow₂ (i+1)] := by
  obtain ⟨w, hw, htw⟩ := (level_iff_odd_multiplier ht i).mp hi
  obtain ⟨v, hv⟩ := hw
  apply Int.modEq_iff_dvd.mpr
  refine ⟨-v, ?_⟩
  rw [htw, hv, pow₂_succ]
  ring

theorem bit_eq_of_modEq {i x y : ℕ} (h : x ≡ y [MOD 2^(i+1)]) :
    x.testBit i = y.testBit i := by
  have hb := congrArg (fun z : ℕ => z.testBit i) (show x % 2^(i+1) = y % 2^(i+1) from h)
  simpa only [Nat.testBit_mod_two_pow, Nat.lt_succ_self, decide_true, Bool.true_and] using hb

/-- If the lower i bits and bit i agree, the full tile residue agrees. -/
theorem mod_tile_eq_of_low_mod_and_bit {i x y : ℕ} (h : x ≡ y [MOD 2^i])
    (hb : x.testBit i = y.testBit i) :
    x ≡ y [MOD 2^(i+1)] := by
  change x % 2^(i+1) = y % 2^(i+1)
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hji : j < i
  · have hj' : j < i+1 := by omega
    have hf := congrArg (fun z : ℕ => z.testBit j) (show x % 2^i = y % 2^i from h)
    simpa only [Nat.testBit_mod_two_pow, hji, hj', decide_true, Bool.true_and] using hf
  · by_cases hji' : j = i
    · subst j
      simpa only [Nat.testBit_mod_two_pow, Nat.lt_succ_self, decide_true, Bool.true_and] using hb
    · have hh : ¬ j < i+1 := by omega
      simp [Nat.testBit_mod_two_pow, hh]

theorem modEq_natCast_pow₂ {i x y : ℕ} :
    ((x:ℤ) ≡ (y:ℤ) [ZMOD pow₂ i]) ↔ x ≡ y [MOD 2^i] := by
  have he : pow₂ i = (((2:ℕ)^i:ℕ):ℤ) := by simp [pow₂]
  rw [he, Int.natCast_modEq_iff]

/-- Flipping bit i under a signed source shift does not use nonnegative t.
If a matched pair has y-x=t, its i-th bits are different. -/
theorem shifted_bit_flip {i x y : ℕ} {t : ℤ} (ht : t ≠ 0)
    (hi : padicValInt 2 t = i) (h : ((y:ℤ)-(x:ℤ)) = t) :
    y.testBit i = !(x.testBit i) := by
  have hmod : (y:ℤ) ≡ pow₂ i + (x:ℤ) [ZMOD pow₂ (i+1)] := by
    have he := (level_modEq_half ht hi).add_right (x:ℤ)
    rw [← h, sub_add_cancel] at he
    exact he
  have hp : pow₂ i + (x:ℤ) = (((2:ℕ)^i+x:ℕ):ℤ) := by simp [pow₂]
  rw [hp] at hmod
  have hbit := bit_eq_of_modEq (modEq_natCast_pow₂.mp hmod)
  rw [Nat.testBit_two_pow_add_eq] at hbit
  exact hbit

/-- No denominator at a crossing vanishes, or has valuation above i,
when the pair of packet bits agree. -/
theorem crossing_nonzero_and_le {i x τ : ℕ} {t : ℤ} (ht : t ≠ 0)
    (hi : padicValInt 2 t = i) (hb : x.testBit i = τ.testBit i) :
    let d := t-(τ:ℤ)+(x:ℤ)
    d ≠ 0 ∧ padicValInt 2 d ≤ i := by
  let d := t-(τ:ℤ)+(x:ℤ)
  have hdv : ¬ pow₂ (i+1) ∣ d := by
    intro he
    have hz := he.modEq_zero_int.add_right (τ:ℤ)
    change d + (τ:ℤ) ≡ 0 + (τ:ℤ) [ZMOD pow₂ (i+1)] at hz
    rw [show d+(τ:ℤ) = t+(x:ℤ) by dsimp [d]; ring, zero_add] at hz
    have heq := hz.symm.trans ((level_modEq_half ht hi).add_right (x:ℤ))
    have hp : pow₂ i + (x:ℤ) = (((2:ℕ)^i+x:ℕ):ℤ) := by simp [pow₂]
    rw [hp] at heq
    have hbit := bit_eq_of_modEq (modEq_natCast_pow₂.mp heq)
    rw [Nat.testBit_two_pow_add_eq, ← hb] at hbit
    cases hxb : x.testBit i <;> simp [hxb] at hbit
  have hdn : d ≠ 0 := fun h => hdv (h ▸ dvd_zero _)
  change d ≠ 0 ∧ padicValInt 2 d ≤ i
  refine ⟨hdn, ?_⟩
  by_contra h
  exact hdv ((padicValInt_dvd_iff (p:=2) (i+1) d).mpr (Or.inr (by omega)))

/-- At a crossing, the exponent h attains i exactly on the advertised
row residue. No sign assumption is made on the retained node t. -/
theorem crossing_eq_level_iff_residue {i x τ : ℕ} {t : ℤ} (ht : t ≠ 0)
    (hi : padicValInt 2 t = i) (hb : x.testBit i = τ.testBit i) :
    padicValInt 2 (t-(τ:ℤ)+(x:ℤ)) = i ↔ x ≡ τ [MOD 2^(i+1)] := by
  let d := t-(τ:ℤ)+(x:ℤ)
  change padicValInt 2 d = i ↔ _
  obtain ⟨hd, hle⟩ := crossing_nonzero_and_le ht hi hb
  have hdt : pow₂ i ∣ t := by
    have he := padicValInt_dvd (p := 2) t
    simpa only [hi, pow₂] using he
  have he : pow₂ i ∣ d ↔ pow₂ i ∣ (x:ℤ)-(τ:ℤ) := by
    have h : d = t+((x:ℤ)-(τ:ℤ)) := by dsimp [d]; ring
    rw [h]
    constructor
    · intro h'
      have hx := Int.dvd_sub h' hdt
      rwa [add_sub_cancel_left] at hx
    · exact Int.dvd_add hdt
  constructor
  · intro hh
    have hdiv : pow₂ i ∣ d :=
      (padicValInt_dvd_iff (p:=2) i d).mpr (Or.inr (by omega))
    have hmod : (τ:ℤ) ≡ (x:ℤ) [ZMOD pow₂ i] := Int.modEq_iff_dvd.mpr (he.mp hdiv)
    exact mod_tile_eq_of_low_mod_and_bit (modEq_natCast_pow₂.mp hmod.symm) hb
  · intro hmod
    have hdvd := (modEq_natCast_pow₂.mpr hmod.symm).dvd
    have hs : pow₂ i ∣ pow₂ (i+1) := ⟨2, pow₂_succ i⟩
    have hh : pow₂ i ∣ d := he.mpr (hs.trans hdvd)
    exact Nat.le_antisymm hle (((padicValInt_dvd_iff (p:=2) i d).mp hh).resolve_left hd)

/-- The precise source notation with the canonical tile representative. -/
theorem crossing_level_iff_tile {i x τ : ℕ} {t : ℤ} (ht : t ≠ 0)
    (hi : padicValInt 2 t = i) (hb : x.testBit i = τ.testBit i) (hτ : τ < 2^(i+1)) :
    padicValInt 2 (t-(τ:ℤ)+(x:ℤ)) = i ↔ x % 2^(i+1) = τ := by
  rw [crossing_eq_level_iff_residue ht hi hb]
  change x % 2^(i+1) = τ % 2^(i+1) ↔ _
  rw [Nat.mod_eq_of_lt hτ]

/-- All ports of a tile have the same bit i. -/
theorem tile_bit (i τ j : ℕ) : (τ+2^(i+1)*j).testBit i = τ.testBit i := by
  apply bit_eq_of_modEq
  change (τ+2^(i+1)*j) % 2^(i+1) = τ % 2^(i+1)
  simp

/-- The exponent in P2 before including the probe's own valuation. -/
def crossingExponent (a i b h : ℕ) : ℕ := a+1-i + b + (b+1)*(i-h)

theorem crossing_exponent_balance {a i b h : ℕ} (hi : i ≤ a) (hh : h ≤ i) :
    a+1+(i+1)*b = crossingExponent a i b h + h*(b+1) := by
  have h1 : a+1-i+i = a+1 := by omega
  have h2 : i-h+h = i := by omega
  unfold crossingExponent
  calc
    a+1+(i+1)*b = (a+1-i+i)+(i+1)*b := congrArg (fun x => x+(i+1)*b) h1.symm
    _ = (a+1-i)+b+(b+1)*i := by ring
    _ = (a+1-i)+b+(b+1)*(i-h+h) := congrArg (fun x => (a+1-i)+b+(b+1)*x) h2.symm
    _ = _ := by ring

theorem integer_scale_balance {a i b h : ℕ} (hi : i ≤ a) (hh : h ≤ i) :
    pow₂ (a+1) * (pow₂ (i+1))^b =
      pow₂ (crossingExponent a i b h) * (pow₂ h)^(b+1) := by
  simp only [pow₂, ← pow_mul, ← pow_add]
  rw [crossing_exponent_balance hi hh]

theorem exponent_lower_and_eq {a i b h : ℕ} (hh : h ≤ i) :
    a+1-i+b ≤ crossingExponent a i b h ∧
      (crossingExponent a i b h = a+1-i+b ↔ h = i) := by
  unfold crossingExponent
  constructor
  · omega
  · constructor
    · intro he
      have hz : (b+1)*(i-h) = 0 := by omega
      rcases Nat.mul_eq_zero.mp hz with hv | hv <;> omega
    · rintro rfl
      simp

section Derivative

theorem grid_modEq_injective {a : ℕ} {v w : ℤ}
    (hv : v ∈ grid a) (hw : w ∈ grid a) (h : v ≡ w [ZMOD pow₂ (a+1)]) :
    v = w := by
  have hb := grid_difference_bounds hw hv
  exact (sub_eq_zero.mp (small_dvd_zero hb.1 hb.2 h.dvd)).symm

theorem valuation_eq_of_modEq_pow₂ {e : ℕ} {v w : ℤ}
    (h : v ≡ w [ZMOD pow₂ e]) (hv : v ≠ 0) (hw : w ≠ 0)
    (hve : padicValInt 2 v ≤ e) (hwe : padicValInt 2 w ≤ e) :
    padicValInt 2 v = padicValInt 2 w := by
  have hvdvd : pow₂ (padicValInt 2 v) ∣ pow₂ e := pow_dvd_pow _ hve
  have hwdvd : pow₂ (padicValInt 2 w) ∣ pow₂ e := pow_dvd_pow _ hwe
  have hjv : pow₂ (padicValInt 2 v) ∣ w :=
    ((h.of_dvd hvdvd).symm.trans (padicValInt_dvd (p:=2) v).modEq_zero_int).dvd
      |> fun hh => by rwa [zero_sub, Int.dvd_neg] at hh
  have hjw : pow₂ (padicValInt 2 w) ∣ v :=
    ((h.of_dvd hwdvd).trans (padicValInt_dvd (p:=2) w).modEq_zero_int).dvd
      |> fun hh => by rwa [zero_sub, Int.dvd_neg] at hh
  exact Nat.le_antisymm
    (((padicValInt_dvd_iff (p:=2) (padicValInt 2 v) w).mp hjv).resolve_left hw)
    (((padicValInt_dvd_iff (p:=2) (padicValInt 2 w) v).mp hjw).resolve_left hv)

/-- For any center, its nonzero differences map bijectively to the
nonzero residues of the full period, preserving valuation. -/
theorem sum_grid_difference_valuations {a : ℕ} {t : ℤ} (ht : t ∈ grid a) :
    (∑ q ∈ (grid a).erase t, padicValInt 2 (t-q)) =
      ∑ r ∈ Finset.Ico 1 (pow₂ (a+1)), padicValInt 2 r := by
  let B := pow₂ (a+1)
  have hB : 0 < B := pow₂_pos _
  have hBa : B = pow₂ a*2 := pow₂_succ _
  let f : ℤ → ℤ := fun q => (t-q) % B
  have hfmod (q : ℤ) : f q ≡ t-q [ZMOD B] := Int.mod_modEq _ _
  have hmem (q : ℤ) (hq : q ∈ (grid a).erase t) : f q ∈ Finset.Ico 1 B := by
    have hlo : 0 ≤ f q := Int.emod_nonneg _ (ne_of_gt hB)
    have hup : f q < B := Int.emod_lt_of_pos _ hB
    have h0 : f q ≠ 0 := by
      intro h
      have hdiv : B ∣ t-q := by
        apply Int.dvd_iff_emod_eq_zero.mpr
        exact h
      have hb := grid_difference_bounds ht (Finset.mem_of_mem_erase hq)
      exact (Finset.ne_of_mem_erase hq) (sub_eq_zero.mp (small_dvd_zero hb.1 hb.2 hdiv)).symm
    exact Finset.mem_Ico.mpr ⟨by omega, hup⟩
  refine Finset.sum_bij (fun q _ => f q) hmem ?_ ?_ ?_
  · intro q hq q' hq' he
    change f q = f q' at he
    have hm' : f q ≡ t-q' [ZMOD B] := by rw [he]; exact hfmod q'
    have hdiff := (hfmod q).symm.trans hm'
    have hs := hdiff.sub_left t
    have hl (v : ℤ) : t-(t-v) = v := by ring
    simp only [hl] at hs
    exact grid_modEq_injective (Finset.mem_of_mem_erase hq) (Finset.mem_of_mem_erase hq') hs
  · intro r hr
    let q := (t+pow₂ a-r) % B - pow₂ a
    have hq : q ∈ grid a := by
      rw [mem_grid]
      have hlo := Int.emod_nonneg (t+pow₂ a-r) (ne_of_gt hB)
      have hup := Int.emod_lt_of_pos (t+pow₂ a-r) hB
      dsimp [q]
      omega
    have hqmod : q ≡ t-r [ZMOD B] := by
      have he := (Int.mod_modEq (t+pow₂ a-r) B).sub_right (pow₂ a)
      rw [show t+pow₂ a-r-pow₂ a = t-r by ring] at he
      exact he
    have htr : t-q ≡ r [ZMOD B] := by
      have he := hqmod.sub_left t
      rwa [show t-(t-r) = r by ring] at he
    have he : f q = r := by
      have he := htr.eq
      rw [Int.emod_eq_of_lt (by have := (Finset.mem_Ico.mp hr).1; omega)
        (Finset.mem_Ico.mp hr).2] at he
      exact he
    have hne : q ≠ t := by
      intro h
      have he0 : f q = 0 := by simp [f, h]
      have hr1 := (Finset.mem_Ico.mp hr).1
      omega
    exact ⟨q, Finset.mem_erase.mpr ⟨hne, hq⟩, he⟩
  · intro q hq
    have hqne : t-q ≠ 0 := sub_ne_zero.mpr ((Finset.ne_of_mem_erase hq).symm)
    have hqv := grid_difference_valuation_le ht (Finset.mem_of_mem_erase hq)
      ((Finset.ne_of_mem_erase hq).symm)
    have hr := Finset.mem_Ico.mp (hmem q hq)
    have hrn : f q ≠ 0 := by omega
    have hrv : padicValInt 2 (f q) ≤ a := by
      by_contra h
      have hdiv : B ∣ f q :=
        (padicValInt_dvd_iff (p:=2) (a+1) (f q)).mpr (Or.inr (by omega))
      exact hrn (Int.eq_zero_of_dvd_of_nonneg_of_lt (by omega) hr.2 hdiv)
    change padicValInt 2 (t-q) = padicValInt 2 (f q)
    exact valuation_eq_of_modEq_pow₂ (hfmod q).symm hqne hrn (by omega) (by omega)

theorem valuation_prod_of_ne_zero {J : Type*} (s : Finset J) (f : J → ℤ)
    (h : ∀ j ∈ s, f j ≠ 0) :
    padicValInt 2 (∏ j ∈ s, f j) = ∑ j ∈ s, padicValInt 2 (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    have hrest : ∀ k ∈ s, f k ≠ 0 := fun k hk => h k (Finset.mem_insert_of_mem hk)
    rw [Finset.prod_insert hj, Finset.sum_insert hj,
      padicValInt.mul (p:=2) (h j (Finset.mem_insert_self _ _)) (Finset.prod_ne_zero_iff.mpr hrest),
      ih hrest]

open scoped Polynomial in
/-- Literal polynomial C of the paper. -/
noncomputable def cauchyPolynomial (a : ℕ) : ℤ[X] :=
  ∏ q ∈ grid a, (Polynomial.X - Polynomial.C q)

theorem cauchy_derivative_eval {a : ℕ} {t : ℤ} (ht : t ∈ grid a) :
    (cauchyPolynomial a).derivative.eval t = ∏ q ∈ (grid a).erase t, (t-q) := by
  rw [cauchyPolynomial,
    ← Finset.mul_prod_erase (grid a) (fun q => Polynomial.X - Polynomial.C q) ht,
    Polynomial.derivative_mul]
  simp [Polynomial.eval_prod]

theorem cauchy_derivative_nonzero {a : ℕ} {t : ℤ} (ht : t ∈ grid a) :
    (cauchyPolynomial a).derivative.eval t ≠ 0 := by
  rw [cauchy_derivative_eval ht]
  exact Finset.prod_ne_zero_iff.mpr
    (fun q hq => sub_ne_zero.mpr (Finset.ne_of_mem_erase hq).symm)

theorem cauchy_derivative_valuation_eq {a : ℕ} {t : ℤ} (ht : t ∈ grid a) :
    padicValInt 2 ((cauchyPolynomial a).derivative.eval t) =
      padicValInt 2 ((cauchyPolynomial a).derivative.eval 0) := by
  rw [cauchy_derivative_eval ht, cauchy_derivative_eval (zero_mem_grid a),
    valuation_prod_of_ne_zero, valuation_prod_of_ne_zero,
    sum_grid_difference_valuations ht, sum_grid_difference_valuations (zero_mem_grid a)]
  · intro q hq
    exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hq).symm
  · intro q hq
    exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hq).symm

/-- C'(t) and C'(0) have the same two-power factor, so their quotient
is a ratio of explicit signed odd units. -/
theorem cauchy_derivative_common_content {a : ℕ} {t : ℤ} (ht : t ∈ grid a) :
    ∃ k : ℕ, ∃ s r : ℤ, Odd s ∧ Odd r ∧
      (cauchyPolynomial a).derivative.eval t = pow₂ k*s ∧
      (cauchyPolynomial a).derivative.eval 0 = pow₂ k*r := by
  obtain ⟨s, hs, he⟩ := integer_odd_factor (cauchy_derivative_nonzero ht)
  obtain ⟨r, hr, her⟩ := integer_odd_factor (cauchy_derivative_nonzero (zero_mem_grid a))
  rw [cauchy_derivative_valuation_eq ht] at he
  exact ⟨_, s, r, hs, hr, he, her⟩

end Derivative

#print axioms grid_difference_valuation_le
#print axioms level_iff_odd_multiplier
#print axioms shifted_bit_flip
#print axioms crossing_nonzero_and_le
#print axioms crossing_level_iff_tile
#print axioms integer_scale_balance
#print axioms sum_grid_difference_valuations
#print axioms cauchy_derivative_common_content

end P1DyadicGrid

