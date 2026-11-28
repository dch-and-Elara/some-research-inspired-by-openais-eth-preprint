import J4R43LiteralOutsideDyadicMoments

/-! The greedy algorithm compares exact bounded-denominator scores by
integer arithmetic. No rational approximation or enumeration of
unfixed global words is an input to this comparison. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators
open IndependentThinning
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6100000

variable {U C : Type*} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]

def colourDigit (colour : U→C) (c : C) (e : U) : ℕ :=
  if colour e=c then 1 else 0

theorem colour_digit_exact (colour : U→C) (c : C) (e : U) :
    (colourDigit colour c e:ℚ)=colourWeight colour c e := by
  by_cases h : colour e=c <;> simp [colourDigit,colourWeight,h]

def meanDigit (B : U→Finset U) (colour : U→C) (D : ℕ) (c : C) : ℕ :=
  ∑ e,colourDigit colour c e*dyadicNumber (fun _=>none) (B e) (required e) D

theorem unconditioned_is_retention (B : U→Finset U) (e : U) :
    localMass (fun _=>none) (B e) (required e)=retention B e := by
  unfold retention
  rw [raw_partial_is_inverse_power]
  simp [matchesPartial,freeRequests]

theorem mean_digit_exact (B : U→Finset U) (colour : U→C) (D : ℕ) (c : C)
    (small : ∀ e,(B e).card≤D) :
    (meanDigit B colour D c:ℚ)=(2:ℚ)^D*meanAt B colour c := by
  unfold meanDigit meanAt
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _=>?_
  rw [colour_digit_exact,(dyadic_numerator_receipt _ _ _ _ (small e)).1,
    unconditioned_is_retention]
  ring

def pairDigit (a : U→Option Bool) (B : U→Finset U) (D : ℕ) (e j : U) : ℕ :=
  if sameRequest B e j then dyadicNumber a (B e∪B j) (bothRequest B e j) (2*D) else 0

theorem pair_digit_exact (a : U→Option Bool) (B : U→Finset U) (D : ℕ) (e j : U)
    (small : ∀ e,(B e).card≤D) :
    (pairDigit a B D e j:ℚ)=(2:ℚ)^(2*D)*twoMoment a B e j := by
  unfold pairDigit twoMoment
  by_cases z : sameRequest B e j
  · rw [if_pos z,if_pos z]
    exact (dyadic_numerator_receipt _ _ _ _ (two_star_scan_bound B D small e j).1).1
  · simp [z]

def scoreFirst (a : U→Option Bool) (B : U→Finset U) (colour : U→C) (D : ℕ) (c : C) : ℕ :=
  ∑ e,colourDigit colour c e*dyadicNumber a (B e) (required e) D

def scoreSecond (a : U→Option Bool) (B : U→Finset U) (colour : U→C) (D : ℕ) (c : C) : ℕ :=
  ∑ e : U,∑ e' : U,colourDigit colour c e*colourDigit colour c e'*pairDigit a B D e e'

def scoreInteger (a : U→Option Bool) (B : U→Finset U) (colour : U→C) (D : ℕ) : ℤ :=
  ∑ c : C,((scoreSecond a B colour D c:ℤ)-
    (2:ℤ)*meanDigit B colour D c*scoreFirst a B colour D c + (meanDigit B colour D c:ℤ)^2)

theorem actual_score_has_common_denominator (a : U→Option Bool) (B : U→Finset U) (colour : U→C) (D : ℕ)
    (small : ∀ e,(B e).card≤D) :
    (scoreInteger a B colour D:ℚ)=(2:ℚ)^(2*D)*localScore a B colour := by
  have p (c : C) : (scoreFirst a B colour D c:ℚ) =
      (2:ℚ)^D*∑ e,colourWeight colour c e*oneMoment a B e := by
    unfold scoreFirst oneMoment
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _=>?_
    rw [colour_digit_exact,(dyadic_numerator_receipt _ _ _ _ (small e)).1]
    ring
  have q (c : C) : (scoreSecond a B colour D c:ℚ) =
      (2:ℚ)^(2*D)*∑ e : U,∑ e' : U,colourWeight colour c e*colourWeight colour c e'*twoMoment a B e e' := by
    unfold scoreSecond
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _=>?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e' _=>?_
    rw [colour_digit_exact,colour_digit_exact,pair_digit_exact a B D e e' small]
    ring
  unfold scoreInteger localScore
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _=>?_
  rw [p,q,mean_digit_exact B colour D c small,conditionalCell]
  have D₂ : (2:ℚ)^(2*D)=((2:ℚ)^D)^2 := by rw [Nat.mul_comm 2 D,pow_mul]
  rw [D₂]
  ring

theorem same_greedy_integer_comparison (a b : U→Option Bool) (B : U→Finset U) (colour : U→C) (D : ℕ)
    (small : ∀ e,(B e).card≤D) :
    scoreInteger a B colour D≤scoreInteger b B colour D ↔ localScore a B colour≤localScore b B colour := by
  rw [←Int.cast_le (R:=ℚ),actual_score_has_common_denominator a B colour D small,
    actual_score_has_common_denominator b B colour D small]
  exact mul_le_mul_iff_right₀ (by positivity)

#print axioms colour_digit_exact
#print axioms unconditioned_is_retention
#print axioms mean_digit_exact
#print axioms pair_digit_exact
#print axioms actual_score_has_common_denominator
#print axioms same_greedy_integer_comparison
end
end J4R43LiteralOutside

