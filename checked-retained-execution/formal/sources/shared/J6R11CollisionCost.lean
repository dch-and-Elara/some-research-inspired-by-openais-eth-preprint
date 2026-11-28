import J6R11CollisionGreedy

/-!
# Integer conditional scores for source label packing

Choose a coordinate alphabet of B words. For each side of an ordered
edge pair the equal-label probability is one of 0, 1/B, 1. The score
therefore requires only one denominator B^2, independent of how many
vertices remain unassigned. The complete candidate scan has the stated
count of ordered pair evaluations. This is not a Turing-machine proof.
-/

open scoped BigOperators Classical

namespace J6R11CollisionCost
open J6R11CollisionGreedy
noncomputable section

section Marginals
variable {I A : Type*} [Fintype A] [Nonempty A]

def marginal (p : I → Option A) (i : I) (a : A) : ℚ :=
  match p i with
  | none => (Fintype.card A : ℚ)⁻¹
  | some b => GuardExpectation.indicator b a

theorem marginal_normalized (p : I → Option A) (i : I) :
    ∑ a, marginal p i a = 1 := by
  cases h : p i with
  | none => simp [marginal,h,nsmul_eq_mul]
  | some b => simp [marginal,h,GuardExpectation.indicator]

omit [Nonempty A] in
theorem marginal_nonneg (p : I → Option A) (i : I) (a : A) :
    0 ≤ marginal p i a := by
  cases h : p i with
  | none => simp [marginal,h]
  | some b => simp [marginal,h,GuardExpectation.indicator]; split <;> norm_num

/-- Integer numerator of a side coincidence with common denominator B. -/
def side (p : I → Option A) (i j : I) : ℕ :=
  if i=j then Fintype.card A else
  match p i,p j with
  | some a,some b => if a=b then Fintype.card A else 0
  | _,_ => 1

omit [Nonempty A] in
theorem side_values (p : I → Option A) (i j : I) :
    side p i j = 0 ∨ side p i j = 1 ∨ side p i j = Fintype.card A := by
  by_cases h : i=j
  · simp [side,h]
  · cases hi : p i with
    | none => cases hj : p j <;> simp [side,h,hi,hj]
    | some a =>
      cases hj : p j with
      | none => simp [side,h,hi,hj]
      | some b => by_cases hab : a=b <;> simp [side,h,hi,hj,hab]

theorem side_le_card (p : I → Option A) (i j : I) :
    side p i j ≤ Fintype.card A := by
  rcases side_values p i j with h|h|h <;> rw [h]
  · exact Nat.zero_le _
  · exact Fintype.card_pos

theorem side_correct (p : I → Option A) (i j : I) :
    equalityMass (marginal p) i j = (side p i j : ℚ)/(Fintype.card A : ℚ) := by
  by_cases h : i=j
  · simp [equalityMass,side,h]
  · rw [equalityMass,if_neg h,side,if_neg h]
    cases hi : p i with
    | none =>
      cases hj : p j with
      | none =>
        simp only [hi,hj,marginal,Nat.cast_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
        field_simp
      | some b =>
        simp only [hi,hj,marginal,Nat.cast_one]
        rw [GuardExpectation.weighted_indicator]
        exact (one_div _).symm
    | some a =>
      cases hj : p j with
      | none =>
        simp only [hi,hj,marginal,Nat.cast_one]
        simp_rw [mul_comm (GuardExpectation.indicator a _)]
        rw [GuardExpectation.weighted_indicator]
        exact (one_div _).symm
      | some b =>
        simp only [hi,hj,marginal]
        rw [GuardExpectation.weighted_indicator]
        by_cases hab : a=b
        · subst b
          simp [GuardExpectation.indicator]
        · simp [GuardExpectation.indicator,hab,Ne.symm hab]

omit [Nonempty A] in
theorem update_marginal [DecidableEq I] [DecidableEq A] (p : I → Option A) (i : I) (b : A) :
    marginal (Function.update p i (some b)) =
      GuardExpectation.fixAt (marginal p) i b := by
  funext j a
  by_cases h : j=i <;> by_cases ha : a=b <;>
    simp [marginal,GuardExpectation.fixAt,Function.update,GuardExpectation.indicator,h,ha]

end Marginals

section Score
variable {E R C A : Type*} [Fintype E] [Fintype A] [Nonempty A]

def contribution (row : E → R) (col : E → C) (p : R⊕C → Option A) (ef : E×E) : ℕ :=
  side p (.inl (row ef.1)) (.inl (row ef.2)) *
    side p (.inr (col ef.1)) (.inr (col ef.2))

def integerScore (row : E → R) (col : E → C) (p : R⊕C → Option A) : ℕ :=
  ∑ ef : E×E, contribution row col p ef

omit [Fintype E] [Nonempty A] in
theorem contribution_values (row : E → R) (col : E → C) (p : R⊕C → Option A) (ef : E×E) :
    contribution row col p ef = 0 ∨ contribution row col p ef = 1 ∨
    contribution row col p ef = Fintype.card A ∨
    contribution row col p ef = (Fintype.card A)^2 := by
  unfold contribution
  rcases side_values p (.inl (row ef.1)) (.inl (row ef.2)) with h|h|h <;>
    rcases side_values p (.inr (col ef.1)) (.inr (col ef.2)) with hk|hk|hk <;>
    simp [h,hk,pow_two]

theorem integerScore_bound (row : E → R) (col : E → C) (p : R⊕C → Option A) :
    integerScore row col p ≤ (Fintype.card E * Fintype.card A)^2 := by
  calc
    _ ≤ ∑ _ : E×E, (Fintype.card A)^2 := by
      unfold integerScore
      apply Finset.sum_le_sum
      intro ef _
      unfold contribution
      rw [pow_two]
      exact Nat.mul_le_mul (side_le_card _ _ _) (side_le_card _ _ _)
    _ = _ := by simp [pow_two]; ac_rfl

/-- Strict upper bound for the number stored in a score register. -/
theorem integerScore_register (row : E → R) (col : E → C) (p : R⊕C → Option A)
    (e b : ℕ) (hM : Fintype.card E < 2^e) (hB : Fintype.card A ≤ 2^b) :
    integerScore row col p < 2^(2*(e+b)) := by
  have H : Fintype.card E * Fintype.card A < 2^(e+b) := calc
    _ < 2^e * Fintype.card A := Nat.mul_lt_mul_of_pos_right hM Fintype.card_pos
    _ ≤ 2^e * 2^b := Nat.mul_le_mul_left _ hB
    _ = _ := pow_add _ _ _ |>.symm
  refine (integerScore_bound row col p).trans_lt ?_
  rw [mul_comm 2 (e+b),pow_mul]
  exact Nat.pow_lt_pow_left H (by decide)

omit [Fintype A] [Nonempty A] in
/-- The source's 64-character alphabet uses 6a bits per label word. The
score (and any partial sum) fits in 2e+12a bits if the edge count is <2^e. -/
theorem printed_register {G : Type*} [Fintype G] [Nonempty G] (a e : ℕ)
    (hG : Fintype.card G = 64) (hM : Fintype.card E < 2^e)
    (row : E → R) (col : E → C) (p : R⊕C → Option (Fin a → G)) :
    integerScore row col p < 2^(2*e+12*a) := by
  have hB : Fintype.card (Fin a → G) ≤ 2^(6*a) := by
    rw [Fintype.card_fun,Fintype.card_fin,hG,pow_mul]
    norm_num
  have h := integerScore_register row col p e (6*a) hM hB
  rwa [show 2*(e+6*a)=2*e+12*a by omega] at h

variable [Fintype R] [Fintype C]

omit [Fintype R] [Fintype C] in
theorem integerScore_correct (row : E → R) (col : E → C) (p : R⊕C → Option A) :
    compressed row col (marginal p) =
      ((integerScore row col p : ℚ) - (Fintype.card E : ℚ)^2) / (Fintype.card A : ℚ)^2 := by
  unfold compressed integerScore contribution
  simp_rw [side_correct,div_mul_div_comm,← pow_two]
  simp only [Fintype.card_prod,Nat.cast_mul,Nat.cast_pow,← pow_two,Nat.cast_sum]
  rw [← Finset.sum_div,div_sub_div_same]

omit [Fintype R] [Fintype C] in
theorem compare_candidates (row : E → R) (col : E → C) (p q : R⊕C → Option A) :
    integerScore row col p ≤ integerScore row col q ↔
      compressed row col (marginal p) ≤ compressed row col (marginal q) := by
  have hB : (0:ℚ) < (Fintype.card A : ℚ)^2 := by
    have ha : (0:ℚ) < Fintype.card A := by exact_mod_cast Fintype.card_pos (α:=A)
    positivity
  simp only [integerScore_correct,div_le_div_iff_of_pos_right hB,sub_le_sub_iff_right,
    Nat.cast_le]

/-- Each exhaustive greedy test evaluates integer scores only. -/
theorem integer_greedy_step (row : E → R) (col : E → C) (p : R⊕C → Option A) (i : R⊕C) :
    ∃ b : A, integerScore row col (Function.update p i (some b)) ≤ integerScore row col p := by
  obtain ⟨b,hb⟩ := greedy_step row col (marginal p) (marginal_nonneg p) (marginal_normalized p) i
  refine ⟨b,(compare_candidates row col _ _).2 ?_⟩
  rw [update_marginal p i b]
  exact hb

omit [Nonempty A] in
theorem exhaustive_pair_count :
    Fintype.card ((R⊕C) × A × (E×E)) =
      (Fintype.card R+Fintype.card C) * Fintype.card A * (Fintype.card E)^2 := by
  simp [pow_two,mul_assoc]

end Score

#print axioms side_correct
#print axioms contribution_values
#print axioms integerScore_register
#print axioms printed_register
#print axioms integerScore_correct
#print axioms compare_candidates
#print axioms integer_greedy_step
#print axioms exhaustive_pair_count

end
end J6R11CollisionCost
