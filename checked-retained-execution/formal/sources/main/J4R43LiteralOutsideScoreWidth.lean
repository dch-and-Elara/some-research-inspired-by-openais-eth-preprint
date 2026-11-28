import J4R43LiteralOutsideScoreInteger

/-! Uniform sizes for the exact integer greedy scores. The same
bounds apply to either candidate, for any partial fixing of the
actual marks. No denominator from the full cube is materialized. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 6000000

variable {U C : Type*} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]
variable (a : U→Option Bool) (B : U→Finset U) (lab : U→C) (D : ℕ)
variable (size : ∀ e,(B e).card≤D)

theorem colourDigit_le_one (c : C) (e : U) : colourDigit lab c e≤1 := by
  unfold colourDigit
  split <;> decide

include size in
theorem first_digits_width (c : C) :
    meanDigit B lab D c≤Fintype.card U*2^D ∧
      scoreFirst a B lab D c≤Fintype.card U*2^D := by
  have f (b : U→Option Bool) :
      ∑ e,colourDigit lab c e*dyadicNumber b (B e) (required e) D≤Fintype.card U*2^D := by
    calc
      _≤∑ _e : U,(2:ℕ)^D := Finset.sum_le_sum (fun e _=>
        (Nat.mul_le_mul (colourDigit_le_one lab c e)
          (dyadic_numerator_receipt b (B e) (required e) D (size e)).2).trans (by simp))
      _=_ := by simp
  exact ⟨f (fun _=>none),f a⟩

include size in
theorem second_digit_width (c : C) :
    scoreSecond a B lab D c≤(Fintype.card U)^2*2^(2*D) := by
  have bd (e f : U) : pairDigit a B D e f≤2^(2*D) := by
    unfold pairDigit
    by_cases t : sameRequest B e f
    · rw [if_pos t]
      exact (dyadic_numerator_receipt a (B e∪B f) (bothRequest B e f) (2*D)
        (two_star_scan_bound B D size e f).1).2
    · simp [t]
  unfold scoreSecond
  calc
    _≤∑ _e : U,∑ _f : U,(2:ℕ)^(2*D) := by
      apply Finset.sum_le_sum
      intro e _
      apply Finset.sum_le_sum
      intro f _
      have k := Nat.mul_le_mul (Nat.mul_le_mul (colourDigit_le_one lab c e) (colourDigit_le_one lab c f)) (bd e f)
      simpa only [Nat.one_mul] using k
    _=_ := by simp [pow_two,mul_assoc]

include size in
theorem integer_score_magnitude (c : C) :
    let v : ℤ := (Fintype.card U:ℤ)*(2:ℤ)^D
    let s : ℤ := scoreSecond a B lab D c
    let m : ℤ := meanDigit B lab D c
    let q : ℤ := scoreFirst a B lab D c
    |s-2*m*q+m^2|≤4*v^2 := by
  let v : ℤ := (Fintype.card U:ℤ)*(2:ℤ)^D
  let s : ℤ := scoreSecond a B lab D c
  let m : ℤ := meanDigit B lab D c
  let q : ℤ := scoreFirst a B lab D c
  have p := first_digits_width a B lab D size c
  have hm : m≤v := by
    change (meanDigit B lab D c:ℤ)≤(Fintype.card U:ℤ)*(2:ℤ)^D
    exact_mod_cast p.1
  have hq : q≤v := by
    change (scoreFirst a B lab D c:ℤ)≤(Fintype.card U:ℤ)*(2:ℤ)^D
    exact_mod_cast p.2
  have hs : s≤v^2 := by
    have L := second_digit_width a B lab D size c
    have e : (2:ℕ)^(2*D)=((2:ℕ)^D)^2 := by rw [Nat.mul_comm 2 D,pow_mul]
    rw [e] at L
    change (scoreSecond a B lab D c:ℤ)≤((Fintype.card U:ℤ)*(2:ℤ)^D)^2
    rw [mul_pow]
    exact_mod_cast L
  have v0 : 0≤v := by dsimp [v]; positivity
  have s0 : 0≤s := by dsimp [s]; positivity
  have m0 : 0≤m := by dsimp [m]; positivity
  have q0 : 0≤q := by dsimp [q]; positivity
  have mv : m*q≤v^2 := by rw [pow_two]; exact mul_le_mul hm hq q0 v0
  have mm : m^2≤v^2 := (sq_le_sq₀ m0 v0).mpr hm
  change |s-2*m*q+m^2|≤4*v^2
  calc
    _≤|s-2*m*q|+|m^2| := abs_add_le _ _
    _≤|s|+|2*m*q|+|m^2| := add_le_add_right (abs_sub _ _) _
    _=s+2*(m*q)+m^2 := by rw [abs_of_nonneg s0,abs_of_nonneg (by positivity : 0≤2*m*q),
      abs_of_nonneg (sq_nonneg m),mul_assoc]
    _≤_ := by linarith only [hs,mv,mm]

include size in
theorem native_greedy_score_width :
    |scoreInteger a B lab D|≤
      (Fintype.card C:ℤ)*(4*((Fintype.card U:ℤ)*(2:ℤ)^D)^2) := by
  let V := (Fintype.card U:ℤ)*(2:ℤ)^D
  let F (c : C) : ℤ := (scoreSecond a B lab D c:ℤ)-
    2*(meanDigit B lab D c:ℤ)*scoreFirst a B lab D c+(meanDigit B lab D c:ℤ)^2
  change |∑ c : C,F c|≤_
  calc
    _≤∑ c : C,|F c| := Finset.abs_sum_le_sum_abs _ _
    _≤∑ _ : C,4*V^2 := Finset.sum_le_sum fun c _=>integer_score_magnitude a B lab D size c
    _=_ := by simp [V]

#print axioms first_digits_width
#print axioms second_digit_width
#print axioms integer_score_magnitude
#print axioms native_greedy_score_width
end
end J4R43LiteralOutside

