
import S11NativeKernel
import Mathlib.Algebra.Ring.GeomSum

noncomputable section
namespace S11

open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]
variable (v : AddValuation K (WithTop ℤ))

theorem valuation_add_strict {x y : K} (h : v x < v y) : v (x+y) = v x := by
  apply le_antisymm _ ((le_min le_rfl h.le).trans (v.map_add _ _))
  by_contra! hh
  have hxy := v.map_add (x+y) (-y)
  rw [add_neg_cancel_right, v.map_neg] at hxy
  exact (not_lt_of_ge hxy) (lt_min hh h)

theorem coefficient_weight {base ratio : K} (hb : 1 ≤ v base) (hr : 1 ≤ v ratio) (b : ℕ) :
    (↑((b+1:ℕ):ℤ) : WithTop ℤ) ≤ v (base * ratio^b) := by
  rw [v.map_mul,v.map_pow]
  have h := add_le_add hb (nsmul_le_nsmul_right hr b)
  simpa only [← WithTop.coe_one, ← WithTop.coe_nsmul, ← WithTop.coe_add,
    Nat.cast_add,Nat.cast_one,nsmul_eq_mul,mul_one,add_comm] using h

/-- Truncation at b+1<p, with the exact divisible remainder. -/
theorem geometric_remainder (h₂ : v (2:K) = 1) {base ratio j : K}
    (hb : 1 ≤ v base) (hr : 1 ≤ v ratio) (hj : 0 ≤ v j) (p : ℕ) (hp : 0 < p) :
    ∃ e : K, 0 ≤ v e ∧
      base/(1-ratio*j) - (∑ b ∈ Finset.range (p-1), base*ratio^b*j^b) = 2^p*e := by
  let x := ratio * j
  have hx : 1 ≤ v x := by
    unfold x
    rw [v.map_mul]
    exact hr.trans (le_add_of_nonneg_right hj)
  have h1 : v (1-x) = 0 := by
    rw [sub_eq_add_neg, valuation_add_strict v, v.map_one]
    rw [v.map_one,v.map_neg]
    exact (by norm_num : (0:WithTop ℤ) < 1).trans_le hx
  have hn : 1-x ≠ 0 := by
    intro H
    rw [H,v.map_zero] at h1
    exact WithTop.top_ne_coe h1
  have he : base/(1-x) - (∑ b ∈ Finset.range (p-1), base*ratio^b*j^b) =
      (base*x^(p-1))/(1-x) := by
    apply (eq_div_iff hn).2
    simp_rw [mul_assoc base, ← mul_pow, ← Finset.mul_sum]
    change (base / (1-x) - base * ∑ b ∈ Finset.range (p-1), x^b) * (1-x) = _
    rw [sub_mul, div_mul_cancel₀ _ hn, mul_assoc, geom_sum_mul_neg]
    ring
  change ∃ e : K, 0 ≤ v e ∧
      base/(1-x) - (∑ b ∈ Finset.range (p-1), base*ratio^b*j^b) = 2^p*e
  rw [he]
  apply (S7.valuation_threshold v h₂ p _).1
  rw [v.map_div, h1, sub_zero]
  simpa [Nat.sub_add_cancel (show 1≤p by omega)] using coefficient_weight v hb hx (p-1)

theorem tile_split (i y : ℕ) :
    y = y % 2^(i+1) + 2^(i+1) * (y / 2^(i+1)) :=
  (Nat.mod_add_div _ _).symm

theorem tile_constant_group_bit (i y : ℕ) :
    (y % 2^(i+1)).testBit i = y.testBit i := by
  simp [Nat.testBit_mod_two_pow]

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- At a crossing tile the i-th bits agree. The valuation of the
    unperturbed basic denominator is at most i. -/
theorem crossing_integer_denominator {t : ℤ} {x y i : ℕ} (ht : t ≠ 0)
    (hi : level t = i) (hb : x.testBit i = y.testBit i) :
    t - (y:ℤ) + x ≠ 0 ∧ level (t-(y:ℤ)+x) ≤ i := by
  let q : ℤ := (2:ℤ)^i
  have hq : 0 < q := by unfold q; positivity
  have hd := padicValInt_dvd (p := 2) t
  rw [show padicValInt 2 t = i from hi] at hd
  obtain ⟨k,hk⟩ : q ∣ t := hd
  have hkodd : ¬ (2:ℤ) ∣ k := by
    rintro ⟨w,hw⟩
    have hh : (2:ℤ)^(i+1) ∣ t := ⟨w,by rw [hk,hw,pow_succ]; unfold q; ring⟩
    exact (by simpa [show padicValInt 2 t = i from hi,ht] using
      (padicValInt_dvd_iff (p:=2) (i+1) t).1 hh)
  have hnd : ¬ (2:ℤ)^(i+1) ∣ t - (y:ℤ)+x := by
    rintro ⟨l,hl⟩
    have hyt : (y:ℤ) = (k-2*l)*q+x := by
      rw [hk,pow_succ] at hl
      unfold q at hk ⊢
      linear_combination -hl
    have hdiv : (y:ℤ)/q = (k-2*l) + (x:ℤ)/q := by
      rw (occs := .pos [1]) [hyt]
      exact Int.mul_add_ediv_right _ _ hq.ne'
    have hpar : (x:ℤ)/q%2 = (y:ℤ)/q%2 := by
      have hh : (x / 2^i)%2 = (y / 2^i)%2 := by
        simp only [Nat.testBit_eq_decide_div_mod_eq, decide_eq_decide] at hb
        have hx := Nat.mod_lt (x / 2^i) (by decide : 0 < 2)
        have hy := Nat.mod_lt (y / 2^i) (by decide : 0 < 2)
        omega
      have hh' : ((x / 2^i)%2:ℕ) = (y / 2^i)%2 := hh
      unfold q
      exact_mod_cast hh'
    rw [hdiv] at hpar
    omega
  exact ⟨fun h => hnd (h ▸ dvd_zero _), by
    by_contra! h
    exact hnd ((padicValInt_dvd_iff (p:=2) (i+1) _).2 (Or.inr h))⟩

/-- Lower valuation survives the native shift by alpha*zeta. -/
theorem crossing_shifted_denominator (h₂ : v (2:K) = 1) {a i : ℕ} (hai : i ≤ a)
    {t : ℤ} {x y : ℕ} (ht : t ≠ 0) (hi : level t = i) (hb : x.testBit i = y.testBit i)
    (ζ : K) (hζ : 0 ≤ v ζ) :
    v (((t-(y:ℤ)+x:ℤ):K) + shiftScale K a * ζ) =
      (↑(level (t-(y:ℤ)+x):ℤ) : WithTop ℤ) := by
  obtain ⟨hn,hl⟩ := crossing_integer_denominator ht hi hb
  have he : v (((t-(y:ℤ)+x:ℤ):K)) = (↑(level (t-(y:ℤ)+x):ℤ) : WithTop ℤ) :=
    S7.valuation_integer v h₂ (t-(y:ℤ)+x) hn
  have hlarge : (↑((a+1:ℕ):ℤ) : WithTop ℤ) ≤ v (shiftScale K a * ζ) := by
    rw [v.map_mul, shiftScale, val_two_pow v h₂]
    exact le_add_of_nonneg_right hζ
  rw [valuation_add_strict v, he]
  exact (by rw [he,WithTop.coe_lt_coe]; omega : v (((t-(y:ℤ)+x:ℤ):K)) < ↑((a+1:ℕ):ℤ)).trans_le hlarge

#print axioms coefficient_weight
#print axioms geometric_remainder
#print axioms tile_constant_group_bit
#print axioms crossing_integer_denominator
#print axioms crossing_shifted_denominator

end S11

