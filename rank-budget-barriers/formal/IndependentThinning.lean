import BangCore
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic

/-! A finite rational product experiment for local edge thinning. Each edge
has an independent fair mark and a biased orientation. The retained signed
variable has an explicit mean and disjoint blocks have zero covariance. -/

namespace IndependentThinning

open scoped BigOperators

abbrev Coin := Bool × Bool
abbrev Outcome (E : Type*) := E → Coin

/-- The first bit is a fair mark. The second bit represents a sign of mean r. -/
def coinWeight (r : ℚ) (z : Coin) : ℚ :=
  if z.2 then (1 + r) / 4 else (1 - r) / 4

theorem coinWeight_nonneg (r : ℚ) (hr : |r| ≤ 1) (z : Coin) : 0 ≤ coinWeight r z := by
  obtain ⟨hl, hu⟩ := abs_le.mp hr
  unfold coinWeight
  split <;> linarith

theorem sum_coinWeight (r : ℚ) : (∑ z : Coin, coinWeight r z) = 1 := by
  rw [Fintype.sum_prod_type]
  simp [Fintype.univ_bool, coinWeight]
  ring

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- Product probability of the complete assignment of marks and orientations. -/
def prob (w : E → ℚ) (ω : Outcome E) : ℚ := ∏ i, coinWeight (w i) (ω i)

omit [DecidableEq E] in
theorem prob_nonneg (w : E → ℚ) (hw : ∀ i, |w i| ≤ 1) (ω : Outcome E) :
    0 ≤ prob w ω :=
  Finset.prod_nonneg (fun i _ => coinWeight_nonneg (w i) (hw i) (ω i))

theorem sum_prob (w : E → ℚ) : (∑ ω : Outcome E, prob w ω) = 1 := by
  calc
    _ = ∏ i, ∑ z : Coin, coinWeight (w i) z := (Fintype.prod_sum _).symm
    _ = _ := by simp only [sum_coinWeight, Finset.prod_const_one]

/-- Fubini's identity for one local factor per coordinate of the experiment. -/
theorem expectation_product (w : E → ℚ) (F : E → Coin → ℚ) :
    (∑ ω : Outcome E, prob w ω * ∏ i, F i (ω i)) =
      ∏ i, ∑ z : Coin, coinWeight (w i) z * F i z := by
  simp only [prob, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i (z : Coin) => coinWeight (w i) z * F i z)).symm

/-- A block of size k prescribes one fair marking pattern of probability (1/2)^k. -/
def retention (B : E → Finset E) (e : E) : ℚ := (1 / 2 : ℚ) ^ (B e).card

/-- Keep e when the unique marked member of its block is e, and return its orientation. -/
def signedValue (B : E → Finset E) (ω : Outcome E) (e : E) : ℚ :=
  if ∀ f ∈ B e, (ω f).1 = decide (f = e) then BangCore.bitSign (ω e).2 else 0

theorem abs_signedValue_le_one (B : E → Finset E) (ω : Outcome E) (e : E) :
    |signedValue B ω e| ≤ 1 := by
  unfold signedValue
  split
  · cases (ω e).2 <;> norm_num [BangCore.bitSign]
  · norm_num

private def localFactor (B : E → Finset E) (e i : E) (z : Coin) : ℚ :=
  if i ∈ B e then
    if z.1 = decide (i = e) then (if i = e then BangCore.bitSign z.2 else 1) else 0
  else 1

private theorem signedValue_as_product (B : E → Finset E) (e : E) (he : e ∈ B e)
    (ω : Outcome E) : signedValue B ω e = ∏ i, localFactor B e i (ω i) := by
  unfold signedValue localFactor
  rw [Fintype.prod_ite_mem, Finset.prod_ite_zero,
    Finset.prod_ite_eq_of_mem' _ _ _ he]
  by_cases h : ∀ i ∈ B e, (ω i).1 = decide (i = e) <;> simp [h]

private theorem expectation_factors (w : E → ℚ) (B : E → Finset E) (e : E) (he : e ∈ B e) :
    (∑ ω : Outcome E, prob w ω * signedValue B ω e) =
      ∏ i, ∑ z : Coin, coinWeight (w i) z * localFactor B e i z := by
  simp only [signedValue_as_product B e he]
  exact expectation_product w (localFactor B e)

omit [Fintype E] in
private theorem local_mean (w : E → ℚ) (B : E → Finset E) (e i : E) :
    (∑ z : Coin, coinWeight (w i) z * localFactor B e i z) =
      if i ∈ B e then (1 / 2 : ℚ) * (if i = e then w i else 1) else 1 := by
  by_cases hmem : i ∈ B e
  · by_cases hi : i = e
    · subst i
      simp [Fintype.sum_prod_type, Fintype.univ_bool, localFactor, hmem, coinWeight, BangCore.bitSign]
      ring
    · simp [Fintype.sum_prod_type, Fintype.univ_bool, localFactor, hmem, hi, coinWeight]
      ring
  · simp [localFactor, hmem, sum_coinWeight]

/-- The prescribed marks have probability 2^(-|B e|), independent of e's orientation. -/
theorem mean_signedValue (w : E → ℚ) (B : E → Finset E) (e : E) (he : e ∈ B e) :
    (∑ ω : Outcome E, prob w ω * signedValue B ω e) = retention B e * w e := by
  rw [expectation_factors w B e he]
  simp only [local_mean, Fintype.prod_ite_mem, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.prod_ite_eq_of_mem' _ _ _ he, retention]

omit [Fintype E] in
private theorem localFactor_outside (B : E → Finset E) (e i : E) (hi : i ∉ B e) (z : Coin) :
    localFactor B e i z = 1 := by simp [localFactor, hi]

/-- Disjoint blocks have exactly factorized mixed second moment. -/
theorem disjoint_cross_moment (w : E → ℚ) (B : E → Finset E) (e f : E)
    (he : e ∈ B e) (hf : f ∈ B f) (hd : Disjoint (B e) (B f)) :
    (∑ ω : Outcome E, prob w ω * (signedValue B ω e * signedValue B ω f)) =
      (∑ ω : Outcome E, prob w ω * signedValue B ω e) *
        ∑ ω : Outcome E, prob w ω * signedValue B ω f := by
  have hfactor (i : E) :
      (∑ z : Coin, coinWeight (w i) z * (localFactor B e i z * localFactor B f i z)) =
        (∑ z : Coin, coinWeight (w i) z * localFactor B e i z) *
          ∑ z : Coin, coinWeight (w i) z * localFactor B f i z := by
    by_cases hi : i ∈ B e
    · have hfi : i ∉ B f := Finset.disjoint_left.mp hd hi
      simp only [localFactor_outside B f i hfi, mul_one, sum_coinWeight]
    · simp only [localFactor_outside B e i hi, one_mul, mul_one, sum_coinWeight]
  calc
    _ = ∑ ω : Outcome E, prob w ω * ∏ i, (localFactor B e i (ω i) * localFactor B f i (ω i)) := by
      simp only [signedValue_as_product B e he, signedValue_as_product B f hf, Finset.prod_mul_distrib]
    _ = ∏ i, ∑ z : Coin, coinWeight (w i) z * (localFactor B e i z * localFactor B f i z) :=
      expectation_product w (fun i z => localFactor B e i z * localFactor B f i z)
    _ = _ := by
      rw [expectation_factors w B e he, expectation_factors w B f hf]
      simp only [hfactor, Finset.prod_mul_distrib]

/-- The covariance about the actual means vanishes for disjoint blocks. -/
theorem disjoint_covariance_zero (w : E → ℚ) (B : E → Finset E) (e f : E)
    (he : e ∈ B e) (hf : f ∈ B f) (hd : Disjoint (B e) (B f)) :
    (∑ ω : Outcome E, prob w ω *
      ((signedValue B ω e - retention B e * w e) * (signedValue B ω f - retention B f * w f))) = 0 := by
  let a := retention B e * w e
  let b := retention B f * w f
  have hp (ω : Outcome E) : prob w ω * ((signedValue B ω e - a) * (signedValue B ω f - b)) =
      prob w ω * (signedValue B ω e * signedValue B ω f) - b * (prob w ω * signedValue B ω e) -
        a * (prob w ω * signedValue B ω f) + (a * b) * prob w ω := by ring
  change (∑ ω : Outcome E, prob w ω * ((signedValue B ω e - a) * (signedValue B ω f - b))) = 0
  simp only [hp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    disjoint_cross_moment w B e f he hf hd, mean_signedValue w B e he, mean_signedValue w B f hf,
    sum_prob, mul_one, a, b]
  ring

#print axioms coinWeight_nonneg
#print axioms sum_coinWeight
#print axioms prob_nonneg
#print axioms sum_prob
#print axioms expectation_product
#print axioms abs_signedValue_le_one
#print axioms mean_signedValue
#print axioms disjoint_cross_moment
#print axioms disjoint_covariance_zero

end IndependentThinning
