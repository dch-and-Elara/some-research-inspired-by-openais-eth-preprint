import J1R43LiteralMarginal

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5100000
set_option linter.unusedSectionVars false

/-! Candidate fixings give exactly uniform or Dirac marginals. A local
test's rational conditional probability has an explicit integer numerator
and denominator r^(number of distinct keys). This proves precision of the
literal evaluator, not exact arithmetic on an arbitrary full product space. -/
namespace J1R43Literal
open scoped BigOperators
open GuardExpectation

section Fixed
variable {P S : Type*} [DecidableEq P] [Fintype S] [DecidableEq S] [Nonempty S]

local notation "r" => Fintype.card S

def partialWeight (known : P → Option S) (i : P) (s : S) : ℚ :=
  match known i with
  | none => (r:ℚ)⁻¹
  | some a => indicator a s

theorem partialWeight_none :
    partialWeight (fun _ : P => (none : Option S)) = fun _ _ => (r:ℚ)⁻¹ :=
  rfl

theorem partialWeight_fix (known : P → Option S) (k : P) (a : S) :
    fixAt (partialWeight known) k a =
      partialWeight (Function.update known k (some a)) := by
  funext i s
  by_cases h : i=k
  · subst i
    simp [fixAt,partialWeight]
  · simp [fixAt,partialWeight,h,Function.update_of_ne]

theorem partialWeight_nonneg (known : P → Option S) (i : P) (s : S) :
    0≤partialWeight known i s := by
  cases hk : known i with
  | none => rw [partialWeight,hk]; positivity
  | some a => simp [partialWeight,hk,indicator]; split <;> norm_num

theorem partialWeight_normalized (known : P → Option S) (i : P) :
    (∑ a, partialWeight known i a)=1 := by
  cases h : known i with
  | none =>
    simp [partialWeight,h,nsmul_eq_mul]
  | some a =>
    simp only [partialWeight,h]
    simpa only [one_mul] using weighted_indicator (fun _ : S => 1) a

def integerWeight (known : P → Option S) (i : P) (s : S) : ℕ :=
  match known i with
  | none => 1
  | some a => if s=a then r else 0

theorem integerWeight_exact (known : P → Option S) (i : P) (s : S) :
    (integerWeight known i s:ℚ)=(r:ℚ)*partialWeight known i s := by
  cases hh : known i with
  | none =>
    simp [integerWeight,partialWeight,hh]
  | some a =>
    by_cases h : s=a <;> simp [integerWeight,partialWeight,indicator,hh,h]

def integerProbability (x : LocalTest P S) (known : P → Option S) : ℕ :=
  ∑ z : x.support → S, (∏ i,integerWeight known i.val (z i)) * (if x.test z then 1 else 0)

theorem integerProbability_exact (x : LocalTest P S) (known : P → Option S) :
    (integerProbability x known:ℚ) =
      (r:ℚ)^x.support.card*x.conditional (partialWeight known) := by
  have hpow : (r:ℚ)^x.support.card = ∏ _i : x.support,(r:ℚ) := by simp
  have hprod (z : x.support → S) :
      (∏ i : x.support,(integerWeight known i.val (z i):ℚ)) =
        (r:ℚ)^x.support.card * productMass
          (fun i : x.support => partialWeight known i.val) z := by
    rw [hpow,productMass,← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _=>integerWeight_exact known i.val (z i))
  unfold integerProbability LocalTest.conditional average
  rw [Nat.cast_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [Nat.cast_mul,Nat.cast_prod,hprod, mul_assoc]
  cases h : x.test z <;> simp [h]

theorem local_probability_le_one (x : LocalTest P S) (known : P → Option S) :
    x.conditional (partialWeight known)≤1 := by
  let w : x.support → S → ℚ := fun i => partialWeight known i.val
  change average w (fun z => if x.test z then 1 else 0)≤1
  calc
    _ ≤ average w (fun _ => 1) := by
      unfold average
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_left _ (productMass_nonneg w (fun i => partialWeight_nonneg known i.val) z)
      cases h : x.test z <;> simp [h]
    _ = _ := average_const w (fun i => partialWeight_normalized known i.val) 1

/-- Exact rational word of a fixed candidate local event, including ties:
the numerator and denominator are both bounded by the support-space size. -/
theorem local_integer_height (x : LocalTest P S) (known : P → Option S) :
    integerProbability x known≤r^x.support.card ∧
    x.conditional (partialWeight known) =
      (integerProbability x known:ℚ)/(r^x.support.card:ℕ) := by
  have hfit := mul_le_mul_of_nonneg_left (local_probability_le_one x known)
    (show 0≤(r:ℚ)^x.support.card by positivity)
  rw [← integerProbability_exact, mul_one] at hfit
  refine ⟨by exact_mod_cast hfit,?_⟩
  have hr : (0:ℚ)<r := by exact_mod_cast (Fintype.card_pos : 0<r)
  push_cast
  rw [integerProbability_exact, mul_comm, mul_div_cancel_right₀ _ (pow_ne_zero _ hr.ne')]

end Fixed

#print axioms partialWeight_none
#print axioms partialWeight_fix
#print axioms partialWeight_nonneg
#print axioms partialWeight_normalized
#print axioms integerProbability_exact
#print axioms local_probability_le_one
#print axioms local_integer_height

end J1R43Literal