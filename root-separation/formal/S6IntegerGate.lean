import S6Feasible
import Mathlib.Data.Nat.Log

namespace Section6

open Finset Filter
open scoped BigOperators Topology
set_option linter.unusedSectionVars false

lemma publishedLambda_eq_clog (n : ℕ) (hn : 0 < n) : publishedLambda n = Nat.clog 2 n := by
  apply le_antisymm
  · apply Nat.ceil_le.mpr
    have h := Nat.le_pow_clog (by decide : 1 < 2) n
    have hp : (n : ℝ) ≤ (2 : ℝ) ^ Nat.clog 2 n := by exact_mod_cast h
    have ht := lg_mono (by exact_mod_cast hn) hp
    simpa only [lg_pow, lg_two, mul_one] using ht
  · apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
    have h : lg (n : ℝ) ≤ (publishedLambda n : ℝ) := Nat.le_ceil _
    have he : lg ((2 : ℝ)^publishedLambda n) = (publishedLambda n : ℝ) := by
      rw [lg_pow,lg_two,mul_one]
    rw [← he] at h
    unfold lg at h
    have hh := (div_le_div_iff_of_pos_right logTwo_pos).mp h
    exact_mod_cast (Real.log_le_log_iff (by exact_mod_cast hn) (by positivity)).mp hh

lemma nat_floor_rat (a b : ℕ) (hb : 0 < b) : ⌊(a : ℝ)/b⌋₊ = a/b := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  apply (Nat.floor_eq_iff (by positivity)).mpr
  constructor
  · apply (le_div_iff₀ hb0).mpr
    exact_mod_cast Nat.div_mul_le_self a b
  · apply (div_lt_iff₀ hb0).mpr
    have h : a < (a/b+1)*b := by simpa [Nat.mul_comm b] using Nat.lt_mul_div_succ a hb
    exact_mod_cast h

lemma publishedQ_eq_div (lam nu : ℕ) (hnu : 0 < nu) :
    publishedQ lam nu = lam/(128*nu) := by
  unfold publishedQ
  have h := nat_floor_rat lam (128*nu) (by positivity)
  simpa using h

def sqrtCeil (lam : ℕ) := if lam.sqrt^2 = lam then lam.sqrt else lam.sqrt+1

lemma sqrt_bounds (lam : ℕ) :
    (lam.sqrt : ℝ) ≤ √(lam : ℝ) ∧ √(lam : ℝ) < (lam.sqrt : ℝ)+1 := by
  have h₁ : (lam.sqrt : ℝ)^2 ≤ lam := by exact_mod_cast Nat.sqrt_le' lam
  have h₂ : (lam : ℝ) < ((lam.sqrt : ℝ)+1)^2 := by exact_mod_cast Nat.lt_succ_sqrt' lam
  exact ⟨(Real.le_sqrt (by positivity) (by positivity)).mpr h₁,
    (Real.sqrt_lt (by positivity) (by positivity)).mpr h₂⟩

lemma sqrtCeil_eq (lam : ℕ) : sqrtCeil lam = ⌈√(lam : ℝ)⌉₊ := by
  unfold sqrtCeil
  split_ifs with h
  · have he : √(lam : ℝ) = (lam.sqrt : ℝ) := by
      have hh : (lam.sqrt : ℝ)^2 = lam := by exact_mod_cast h
      rw [← hh, Real.sqrt_sq (by positivity)]
    rw [he, Nat.ceil_natCast]
  · symm
    apply (Nat.ceil_eq_iff (by omega)).mpr
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    refine ⟨?_,(sqrt_bounds lam).2.le⟩
    have hh : (lam.sqrt : ℝ)^2 < lam := by
      exact_mod_cast lt_of_le_of_ne (Nat.sqrt_le' lam) h
    have hr := Real.sqrt_lt_sqrt (by positivity) hh
    rwa [Real.sqrt_sq (by positivity)] at hr

lemma publishedRGroups_eq_div (lam nu : ℕ) (hnu : 0 < nu) :
    publishedRGroups lam nu = lam.sqrt / nu^2 := by
  have hs := sqrt_bounds lam
  let d := nu^2
  let r := lam.sqrt/d
  have hd : 0 < d := by unfold d; positivity
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hdc : (d : ℝ) = (nu : ℝ)^2 := by simp [d]
  unfold publishedRGroups
  rw [← hdc]
  change _ = r
  apply (Nat.floor_eq_iff (by positivity)).mpr
  · constructor
    · apply (le_div_iff₀ hdp).mpr
      exact (show (r : ℝ)*d ≤ lam.sqrt by exact_mod_cast Nat.div_mul_le_self lam.sqrt d).trans hs.1
    · apply (div_lt_iff₀ hdp).mpr
      have h : lam.sqrt+1 ≤ (r+1)*d := by
        have ht := Nat.lt_mul_div_succ lam.sqrt hd
        rw [Nat.mul_comm] at ht
        exact ht
      exact hs.2.trans_le (by exact_mod_cast h)

def integerStart (Q R r : ℕ) : ℕ := (Q*(r-1)-r*(R-1))/(2*r)

lemma centeredStart_eq_integerStart {Q R r : ℕ} (hr : 2 ≤ r) (hR : 1 ≤ R)
    (hQR : 6*R ≤ Q) : centeredStart Q R r = integerStart Q R r := by
  have hr' : 1 ≤ r := by omega
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hQr : (6 : ℝ)*R ≤ Q := by exact_mod_cast hQR
  have hel := (spectralP_bounds hr).1
  have hpos : 0 ≤ (Q : ℝ)*spectralP r - ((R : ℝ)-1)/2 := by
    linarith only [hQr,hR',mul_le_mul_of_nonneg_left hel (show (0:ℝ) ≤ Q by positivity)]
  have hformula : (Q : ℝ)*spectralP r - ((R : ℝ)-1)/2 =
      ((Q : ℝ)*((r : ℝ)-1) - (r : ℝ)*((R : ℝ)-1))/(2*r) := by
    unfold spectralP
    field_simp [hr0.ne']
  have hNum : r*(R-1) ≤ Q*(r-1) := by
    rw [hformula] at hpos
    have h := (le_div_iff₀ (by positivity : 0 < 2*(r : ℝ))).mp hpos
    have h' : (r : ℝ)*((R : ℝ)-1) ≤ (Q : ℝ)*((r : ℝ)-1) := by linarith only [h]
    exact_mod_cast (by
      simpa only [Nat.cast_sub hr', Nat.cast_sub hR, Nat.cast_one, Nat.cast_mul] using h' :
      ((r*(R-1) : ℕ) : ℝ) ≤ ((Q*(r-1) : ℕ) : ℝ))
  unfold centeredStart integerStart
  have he : ((Q*(r-1)-r*(R-1) : ℕ) : ℝ) =
      (Q : ℝ)*((r : ℝ)-1) - (r : ℝ)*((R : ℝ)-1) := by
    push_cast [Nat.cast_sub hNum, Nat.cast_sub hr', Nat.cast_sub hR]
    rfl
  rw [hformula, ← he]
  exact (by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      nat_floor_rat (Q*(r-1)-r*(R-1)) (2*r) (by omega))

def tailNumerator (Q r : ℕ) (win : Finset ℕ) : ℕ :=
  ∑ j ∈ (range (Q+1)).filter (· ∉ win), Q.choose j * (r-1)^j * (r+1)^(Q-j)

theorem binomial_integer_tail {Q r : ℕ} (hr : 2 ≤ r) (win : Finset ℕ) :
    ∑ j ∈ (range (Q+1)).filter (· ∉ win), binMass Q (spectralP r) j =
      (tailNumerator Q r win : ℝ)/(2*r)^Q := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hr1 : 1 ≤ r := by omega
  have h : 1 - spectralP r = ((r : ℝ)+1)/(2*r) := by
    unfold spectralP
    field_simp [hr0.ne']
    ring
  unfold tailNumerator
  rw [Nat.cast_sum, sum_div]
  apply sum_congr rfl
  intro j hj
  have hjQ : j ≤ Q := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hj).1)
  unfold binMass
  rw [h, spectralP, div_pow, div_pow]
  push_cast [Nat.cast_sub hr1]
  rw [mul_assoc, div_mul_div_comm, ← pow_add, Nat.add_sub_cancel' hjQ, ← mul_div_assoc]
  ring

/-- The frozen guard can be checked by one integer comparison. -/
theorem integer_tail_guard {Q r b lam : ℕ} (hr : 2 ≤ r) (hb : 0 < b) (hL : 0 < lam)
    (win : Finset ℕ) :
    (∑ j ∈ (range (Q+1)).filter (· ∉ win), binMass Q (spectralP r) j ≤
      1/((b : ℝ)*r^2*lam)) ↔
      tailNumerator Q r win * (b*r^2*lam) ≤ (2*r)^Q := by
  rw [binomial_integer_tail hr]
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hL0 : (0 : ℝ) < lam := by exact_mod_cast hL
  rw [div_le_div_iff₀ (by positivity) (by positivity),one_mul]
  exact_mod_cast (Iff.rfl :
    (((tailNumerator Q r win : ℕ) : ℝ) * (((b*r^2*lam : ℕ) : ℝ)) ≤
      (((2*r)^Q : ℕ) : ℝ)) ↔ _)

#print axioms publishedLambda_eq_clog
#print axioms publishedQ_eq_div
#print axioms sqrtCeil_eq
#print axioms publishedRGroups_eq_div
#print axioms centeredStart_eq_integerStart
#print axioms integer_tail_guard

end Section6



