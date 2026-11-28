import ColorAlphabetFinite
import ColorAlphabetLower
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Lattice

open scoped BigOperators Polynomial
open Filter Topology

namespace Reconstruction.ColorAlphabet

noncomputable section

def rankSet (ternary : Bool) (q r : ℕ) (a : Fin q → ℚ) : Set ℕ :=
  {k | ∃ (m : ℕ) (C : Matrix (Fin m) (Word (fun _ : Fin q => Fin r)) ℚ)
    (P : Matrix (Word (fun _ : Fin q => Fin r)) (Word (fun _ : Fin q => Fin r)) ℚ[X]),
    FeasibleZero a C P ∧
      (ternary = true → ∀ i v, C i v = -1 ∨ C i v = 0 ∨ C i v = 1) ∧ C.rank = k}

def minimumRank (ternary : Bool) (q r : ℕ) (a : Fin q → ℚ) : ℕ :=
  sInf (rankSet ternary q r a)

theorem minimumRank_attained (ternary : Bool) (q r : ℕ) (hr : 0 < r) (a : Fin q → ℚ) :
    minimumRank ternary q r a ∈ rankSet ternary q r a := by
  obtain ⟨m, C, P, hP, hT, -⟩ := ternary_finite_upper q r hr a
  exact Nat.sInf_mem ⟨C.rank, m, C, P, hP, fun _ => hT, rfl⟩

def lowerFraction (q r : ℕ) : ℝ :=
  ((r : ℝ)-1)/(2*(r : ℝ)-1) -
    ∑ j ∈ Finset.range (r-1), (((j+1 : ℕ) : ℝ)/(r : ℝ))^(2*q) /
      (4*((j+1 : ℕ) : ℝ)^2-1)

def upperNumerator (r : ℕ) : ℕ := if r % 2 = 0 then r-1 else r
def upperDenominator (r : ℕ) : ℕ := if r % 2 = 0 then 2*r-1 else 2*r+1
def offset (r : ℕ) : ℕ := if r % 2 = 0 then r/2 else (r+1)/2

def upperFraction (q r : ℕ) : ℝ :=
  (upperNumerator r : ℝ) / (upperDenominator r : ℝ) *
    (1 - ((offset r : ℝ)/(r : ℝ)^2)^q)

private theorem offset_le (r : ℕ) (hr : 0 < r) : offset r ≤ r := by
  unfold offset
  split_ifs <;> omega

private theorem lower_fraction_le (ternary : Bool) (q r : ℕ) (hr : 0 < r) (a : Fin q → ℚ) :
    lowerFraction q r ≤ (minimumRank ternary q r a : ℝ)/(r : ℝ)^(2*q) := by
  obtain ⟨m, C, P, hP, -, hrank⟩ := minimumRank_attained ternary q r hr a
  have hQ := uniform_rank_lower_polynomial q r a C P hP
  rw [uniform_converse_telescoped q r hr, hrank] at hQ
  have hR := (Rat.cast_mono (K := ℝ)) hQ
  push_cast [rate] at hR
  have hp : 0 < (r : ℝ)^(2*q) := pow_pos (by exact_mod_cast hr) _
  apply (le_div_iff₀ hp).mpr
  convert hR using 1
  rw [lowerFraction, sub_mul, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [div_pow]
  field_simp [hp.ne']
  push_cast
  rfl

private theorem minimumRank_upper_clear (ternary : Bool) (q r : ℕ) (hr : 0 < r)
    (a : Fin q → ℚ) :
    upperDenominator r * minimumRank ternary q r a ≤
      upperNumerator r * (r^(2*q) - offset r ^ q) := by
  obtain ⟨m, C, P, hP, hT, h⟩ := ternary_finite_upper q r hr a
  have hmin : minimumRank ternary q r a ≤ C.rank :=
    Nat.sInf_le ⟨m, C, P, hP, fun _ => hT, rfl⟩
  exact (Nat.mul_le_mul_left _ hmin).trans h

private theorem upper_den_pos (r : ℕ) (hr : 0 < r) : 0 < upperDenominator r := by
  unfold upperDenominator
  split_ifs <;> omega

private theorem upper_fraction_ge (ternary : Bool) (q r : ℕ) (hr : 0 < r) (a : Fin q → ℚ) :
    (minimumRank ternary q r a : ℝ)/(r : ℝ)^(2*q) ≤ upperFraction q r := by
  have ole : offset r ^ q ≤ r^(2*q) := by
    rw [pow_mul]
    apply Nat.pow_le_pow_left _ q
    exact (offset_le r hr).trans (by nlinarith)
  have h := minimumRank_upper_clear ternary q r hr a
  have hc : ((upperDenominator r : ℕ) : ℝ) * (minimumRank ternary q r a : ℝ) ≤
      (upperNumerator r : ℝ) * ((r : ℝ)^(2*q) - (offset r : ℝ)^q) := by
    exact_mod_cast (show upperDenominator r * minimumRank ternary q r a ≤
      upperNumerator r * (r^(2*q) - offset r ^ q) from h)
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hp := pow_pos hr' (2*q)
  have hd : (0 : ℝ) < upperDenominator r := by exact_mod_cast upper_den_pos r hr
  have hh := ((le_div_iff₀ hd).mpr (by simpa only [mul_comm (upperDenominator r : ℝ)] using hc))
  apply (div_le_iff₀ hp).mpr
  refine hh.trans_eq ?_
  rw [upperFraction, div_pow, ← pow_mul]
  field_simp [hp.ne', hd.ne']

/-- The finite converse and the explicit even/odd upper bounds, normalized
by the number of physical coordinates. Both choices of rank class are covered. -/
theorem theorem2_finite (ternary : Bool) (q r : ℕ) (hr : 0 < r) (a : Fin q → ℚ) :
    lowerFraction q r ≤ (minimumRank ternary q r a : ℝ)/(r : ℝ)^(2*q) ∧
      (minimumRank ternary q r a : ℝ)/(r : ℝ)^(2*q) ≤ upperFraction q r :=
  ⟨lower_fraction_le ternary q r hr a, upper_fraction_ge ternary q r hr a⟩

/-- The normalized receiver-order converse converges to its leading term
for every fixed positive alphabet size. -/
theorem lowerFraction_tendsto (r : ℕ) (hr : 0 < r) :
    Tendsto (fun q => lowerFraction q r) atTop (𝓝 (((r : ℝ)-1)/(2*r-1))) := by
  have h (j : ℕ) (hj : j ∈ Finset.range (r-1)) :
      Tendsto (fun q => (((j+1 : ℕ) : ℝ)/(r : ℝ))^(2*q) /
        (4*((j+1 : ℕ) : ℝ)^2-1)) atTop (𝓝 0) := by
    have hp : 0 < (r : ℝ) := by exact_mod_cast hr
    have hlt : (((j+1 : ℕ) : ℝ)/(r : ℝ)) < 1 := by
      apply (div_lt_one hp).mpr
      exact_mod_cast (show j+1 < r from by have := Finset.mem_range.mp hj; omega)
    have hn : 0 ≤ (((j+1 : ℕ) : ℝ)/(r : ℝ)) := by positivity
    have hs : (((j+1 : ℕ) : ℝ)/(r : ℝ))^2 < 1 := by nlinarith
    simpa only [pow_mul, zero_div] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg _) hs).div_const (4*((j+1 : ℕ) : ℝ)^2-1)
  have hs := tendsto_finset_sum (Finset.range (r-1)) h
  simpa [lowerFraction] using tendsto_const_nhds.sub hs

theorem upperFraction_tendsto (r : ℕ) (hr : 2 ≤ r) :
    Tendsto (fun q => upperFraction q r) atTop
      (𝓝 ((upperNumerator r : ℝ)/(upperDenominator r : ℝ))) := by
  have hp : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hle : (offset r : ℝ) ≤ r := by exact_mod_cast offset_le r (by omega)
  have hlt : (offset r : ℝ)/(r : ℝ)^2 < 1 := by
    apply (div_lt_one (sq_pos_of_pos hp)).mpr
    have h2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith
  have hn : 0 ≤ (offset r : ℝ)/(r : ℝ)^2 := by positivity
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hn hlt).const_sub 1
  simpa [upperFraction] using ht.const_mul ((upperNumerator r : ℝ)/(upperDenominator r : ℝ))

/-- Theorem 2's common limit for the unrestricted rational and ternary rank minima. -/
theorem theorem2_even_limit (ternary : Bool) (r : ℕ) (hr : 2 ≤ r) (he : r % 2 = 0)
    (a : (q : ℕ) → Fin q → ℚ) :
    Tendsto (fun q => (minimumRank ternary q r (a q) : ℝ)/(r : ℝ)^(2*q))
      atTop (𝓝 (((r : ℝ)-1)/(2*r-1))) := by
  have hl := lowerFraction_tendsto r (by omega)
  have hu := upperFraction_tendsto r hr
  have hd : 1 ≤ 2*r := by omega
  have hm : 1 ≤ r := by omega
  simp only [upperNumerator, upperDenominator, he, if_true, Nat.cast_sub hm, Nat.cast_sub hd,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu
    (fun q => (theorem2_finite ternary q r (by omega) (a q)).1)
    (fun q => (theorem2_finite ternary q r (by omega) (a q)).2)

/-- The difference between the explicit upper and converse fractions is
nonnegative at every finite dimension and converges to the stated odd gap. -/
theorem odd_alphabet_gap (r : ℕ) (hr : 3 ≤ r) (ho : r % 2 = 1) :
    (∀ q, 0 ≤ upperFraction q r - lowerFraction q r) ∧
      Tendsto (fun q => upperFraction q r - lowerFraction q r)
        atTop (𝓝 (1/(4*(r : ℝ)^2-1))) := by
  refine ⟨fun q => ?_, ?_⟩
  · have h := theorem2_finite true q r (by omega) (fun _ => 0)
    exact sub_nonneg.mpr (h.1.trans h.2)
  · have hu := upperFraction_tendsto r (by omega)
    have hl := lowerFraction_tendsto r (by omega)
    have ho' : r % 2 ≠ 0 := by omega
    simp only [upperNumerator, upperDenominator, ho', if_false, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one] at hu
    convert hu.sub hl using 2
    have h3 : (3 : ℝ) ≤ r := by exact_mod_cast hr
    field_simp (disch := nlinarith) <;> ring


/-- The construction gives the unnormalized finite bounds of Theorem 2. -/
theorem theorem2_ternary_construction (q r : ℕ) (hr : 0 < r) (a : Fin q → ℚ) :
    ∃ (m : ℕ) (C : Matrix (Fin m) (Word (fun _ : Fin q => Fin r)) ℚ)
      (P : Matrix (Word (fun _ : Fin q => Fin r)) (Word (fun _ : Fin q => Fin r)) ℚ[X]),
      FeasibleZero a C P ∧ (∀ i v, C i v = -1 ∨ C i v = 0 ∨ C i v = 1) ∧
        (C.rank : ℝ) ≤
          if r % 2 = 0 then
            ((r : ℝ)-1)/(2*(r : ℝ)-1) * ((r : ℝ)^(2*q)-((r/2 : ℕ) : ℝ)^q)
          else
            (r : ℝ)/(2*(r : ℝ)+1) * ((r : ℝ)^(2*q)-(((r+1)/2 : ℕ) : ℝ)^q) := by
  obtain ⟨m, C, P, hP, hter, h⟩ := ternary_finite_upper q r hr a
  refine ⟨m, C, P, hP, hter, ?_⟩
  change upperDenominator r * C.rank ≤ upperNumerator r * (r^(2*q) - offset r ^ q) at h
  have ole : offset r ^ q ≤ r^(2*q) := by
    rw [pow_mul]
    apply Nat.pow_le_pow_left _ q
    exact (offset_le r hr).trans (by nlinarith)
  have hc : (upperDenominator r : ℝ) * (C.rank : ℝ) ≤
      (upperNumerator r : ℝ) * ((r : ℝ)^(2*q) - (offset r : ℝ)^q) := by exact_mod_cast h
  have hd : (0 : ℝ) < upperDenominator r := by exact_mod_cast upper_den_pos r hr
  have hf := (le_div_iff₀ hd).mpr (by simpa only [mul_comm (upperDenominator r : ℝ)] using hc)
  have h1 : 1 ≤ r := hr
  have h2 : 1 ≤ 2*r := by omega
  by_cases he : r % 2 = 0 <;>
    simpa [he, upperNumerator, upperDenominator, offset, Nat.cast_sub h1, Nat.cast_sub h2,
      div_mul_eq_mul_div] using hf

/-- For odd alphabets the finite upper and lower certificates are strictly
separated once there are at least two slots. -/
theorem odd_alphabet_gap_strict (q r : ℕ) (hq : 2 ≤ q) (hr : 3 ≤ r) (ho : r % 2 = 1) :
    lowerFraction q r < upperFraction q r := by
  have hr' : (3 : ℝ) ≤ r := by exact_mod_cast hr
  have hp : (0 : ℝ) < r := by linarith
  let z : ℝ := (offset r : ℝ)/(r : ℝ)^2
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have ho' : r % 2 ≠ 0 := by omega
  have hm : 3 * offset r ≤ 2*r := by simp only [offset, ho', if_false]; omega
  have hm' : (3 : ℝ) * (offset r : ℝ) ≤ 2*r := by exact_mod_cast hm
  have hz : z ≤ 2 / (3*(r : ℝ)) := by
    dsimp [z]
    apply (div_le_div_iff₀ (sq_pos_of_pos hp) (by positivity)).mpr
    nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hm')]
  have hz1 : z ≤ 1 := hz.trans (by apply (div_le_one (by positivity)).mpr; linarith)
  have hpow : z^q ≤ (2/(3*(r : ℝ)))^2 :=
    (pow_le_pow_of_le_one hz0 hz1 hq).trans (pow_le_pow_left₀ hz0 hz _)
  have hn : (0 : ℝ) ≤ (r : ℝ)/(2*(r : ℝ)+1) := by positivity
  have hpos : 0 < (2*(r : ℝ)+1)*(2*(r : ℝ)-1) :=
    mul_pos (by positivity) (by linarith)
  have hg : (r : ℝ)/(2*(r : ℝ)+1)*(2/(3*(r : ℝ)))^2 <
      (r : ℝ)/(2*(r : ℝ)+1) - ((r : ℝ)-1)/(2*(r : ℝ)-1) := by
    have hc : (r : ℝ)/(2*(r : ℝ)+1)*(2/(3*(r : ℝ)))^2 =
        4/(9*(r : ℝ)*(2*(r : ℝ)+1)) := by
      field_simp (disch := positivity) <;> ring
    have hd : (r : ℝ)/(2*(r : ℝ)+1) - ((r : ℝ)-1)/(2*(r : ℝ)-1) =
        1/((2*(r : ℝ)+1)*(2*(r : ℝ)-1)) := by
      field_simp (disch := linarith) <;> ring
    rw [hc, hd]
    apply (div_lt_div_iff₀ (by positivity) hpos).mpr
    nlinarith [mul_pos (show 0 < 2*(r : ℝ)+1 by positivity)
      (show 0 < (r : ℝ)+4 by linarith)]
  have hlo : lowerFraction q r ≤ ((r : ℝ)-1)/(2*(r : ℝ)-1) := by
    apply sub_le_self
    apply Finset.sum_nonneg
    intro j hj
    have hj' : 1 ≤ ((j+1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ j+1)
    exact div_nonneg (pow_nonneg (by positivity) _) (by nlinarith)
  have hstrict := (mul_le_mul_of_nonneg_left hpow hn).trans_lt hg
  apply hlo.trans_lt
  simp only [upperFraction, upperNumerator, upperDenominator, ho', if_false, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  change ((r : ℝ)-1)/(2*(r : ℝ)-1) < (r : ℝ)/(2*(r : ℝ)+1) * (1-z^q)
  linarith only [hstrict]

end

end Reconstruction.ColorAlphabet
