import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Find
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic

/-! Width-three numerical admission from the original MAIN
3582–3594 and 3813–3847. The candidate test is the actual integer
comparison; there is no assumption that a hand-retuned base grows. -/
namespace F5R63.Sparsify
set_option autoImplicit false

def sourceLambda (n : ℕ) : ℕ := Nat.clog 2 n

def sourceNu (n : ℕ) : ℕ := Nat.clog 2 (sourceLambda n)

def validSourceIndex (n s : ℕ) : Prop := s^2*(sourceNu n)^4 ≤ sourceLambda n

instance (n s : ℕ) : Decidable (validSourceIndex n s) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- The maximum in MAIN 3586–3589. For n≥20, every legal candidate
lies in this exact finite search interval; this does not meter a search. -/
def sourceS (n : ℕ) : ℕ :=
  Nat.findGreatest (validSourceIndex n) (sourceLambda n)

theorem source_lambda_at_least_five (n : ℕ) (hn : 20≤n) : 5≤sourceLambda n := by
  change 4 < Nat.clog 2 n
  exact (Nat.lt_clog_iff_pow_lt (by decide : 1 < (2:ℕ))).2 (by omega)

theorem source_nu_at_least_three (n : ℕ) (hn : 20≤n) : 3≤sourceNu n := by
  change 2 < Nat.clog 2 (sourceLambda n)
  have h := source_lambda_at_least_five n hn
  exact (Nat.lt_clog_iff_pow_lt (by decide : 1 < (2:ℕ))).2 (by omega)

private theorem source_index_bounded (n s : ℕ) (hn : 20≤n)
    (h : validSourceIndex n s) : s ≤ sourceLambda n := by
  have v : 1≤sourceNu n := by have := source_nu_at_least_three n hn; omega
  have v4 := Nat.one_le_pow 4 (sourceNu n) v
  by_cases sz : s=0
  · simp [sz]
  have sv : 1≤s := by omega
  have sv2 : s≤s^2 := by simpa only [pow_one] using
    (Nat.pow_le_pow_right sv (by decide : 1≤2))
  have product := Nat.mul_le_mul sv2 v4
  exact (by simpa only [Nat.mul_one] using product : s≤s^2*(sourceNu n)^4).trans h

theorem sourceS_is_exact_largest_index (n : ℕ) (hn : 20≤n) :
    validSourceIndex n (sourceS n) ∧ ∀ s, validSourceIndex n s → s≤sourceS n := by
  have base : validSourceIndex n 0 := by simp [validSourceIndex]
  exact ⟨Nat.findGreatest_spec (Nat.zero_le _) base,
    fun s hs => Nat.le_findGreatest (source_index_bounded n s hn hs) hs⟩

private theorem fourth_growth (n : ℕ) (h : 6≤n) : (n+1)^4≤2*n^4 := by
  have lin : 6*(n+1)≤7*n := by omega
  have prod := Nat.pow_le_pow_left lin 4
  simp only [Nat.mul_pow,show (6:ℕ)^4=1296 by decide,
    show (7:ℕ)^4=2401 by decide] at prod
  omega

private theorem fourth_vs_power_two (j : ℕ) : 4*(21+j)^4 ≤ 2^(20+j) := by
  induction j with
  | zero => decide
  | succ j ih =>
    have grow := Nat.mul_le_mul_left 4 (fourth_growth (21+j) (by omega))
    calc
      4*(21+(j+1))^4 = 4*((21+j)+1)^4 := by rw [Nat.add_assoc]
      _ ≤ 2*(4*(21+j)^4) := by simpa only [Nat.mul_left_comm] using grow
      _ ≤ 2*(2^(20+j)) := Nat.mul_le_mul_left _ ih
      _ = 2^(20+(j+1)) := by rw [← Nat.add_assoc,pow_succ,Nat.mul_comm]

/-- A sufficient, not optimal, concrete eventual entrance. It verifies
the integer condition for the actual candidate s=2. -/
theorem large_source_index_gate (n : ℕ) (hn : (2:ℕ)^((2:ℕ)^20)<n) :
    validSourceIndex n 2 := by
  have ln : (2:ℕ)^20 < sourceLambda n :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1 < (2:ℕ))).2 hn
  have nv : 20<sourceNu n :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1 < (2:ℕ))).2 ln
  let j := sourceNu n-21
  have rew : sourceNu n=21+j := by dsimp only [j]; omega
  have hl : (2:ℕ)^(20+j)<sourceLambda n := by
    apply (Nat.lt_clog_iff_pow_lt (by decide : 1 < (2:ℕ))).1
    change 20+j<sourceNu n
    omega
  unfold validSourceIndex
  rw [rew]
  exact (fourth_vs_power_two j).trans hl.le

theorem large_source_enters_sparsifier (n : ℕ) (hn : (2:ℕ)^((2:ℕ)^20)<n) :
    20≤n ∧ 2≤sourceS n := by
  have p : (2:ℕ)^5 ≤ (2:ℕ)^((2:ℕ)^20) :=
    Nat.pow_le_pow_right (by decide) (by decide)
  have h20 : 20≤n := (show (20:ℕ)≤2^5 by decide).trans (p.trans hn.le)
  exact ⟨h20,(sourceS_is_exact_largest_index n h20).2 2 (large_source_index_gate n hn)⟩

/-- Exact width-three specializations of MAIN's C and Γ. -/
def sourceC3 (M : ℕ) : ℕ := 4*(1+3*M)

def sourceGamma3 : ℕ := 2*(3^(3-1)-1)

def sourceH3 (M : ℕ) : ℕ := Nat.clog 2 (4*sourceC3 M*M)

def successfulSourceExponent (s a : ℕ) : Prop :=
  sourceGamma3≤2^a ∧ sourceGamma3*sourceH3 (2^a)*s≤2^a

instance (s a : ℕ) : Decidable (successfulSourceExponent s a) :=
  inferInstanceAs (Decidable (_ ≤ _ ∧ _ ≤ _))

theorem printed_width_three_gamma : sourceGamma3=16 := rfl

theorem printed_candidate_is_exact_rational_comparison (s a : ℕ) (hs : 0<s) :
    successfulSourceExponent s a ↔
      sourceGamma3≤2^a ∧
      ((sourceGamma3*sourceH3 (2^a):ℕ):ℚ) ≤ (1/(s:ℚ))*(((2:ℕ)^a:ℕ):ℚ) := by
  have hp : (0:ℚ)<(s:ℚ) := by exact_mod_cast hs
  have nonzero : (s:ℚ)≠0 := ne_of_gt hp
  have rwM : (1/(s:ℚ))*(((2:ℕ)^a:ℕ):ℚ) = (((2:ℕ)^a:ℕ):ℚ)/(s:ℚ) := by
    field_simp
  rw [rwM,le_div_iff₀ hp]
  unfold successfulSourceExponent
  norm_cast

private theorem square_growth (n : ℕ) (h : 4≤n) : (n+1)^2≤2*n^2 := by
  have lin : 4*(n+1)≤5*n := by omega
  have prod := Nat.pow_le_pow_left lin 2
  simp only [Nat.mul_pow,show (4:ℕ)^2=16 by decide,
    show (5:ℕ)^2=25 by decide] at prod
  omega

private theorem square_vs_power_two (j : ℕ) : (4+j)^2 ≤ 2^(4+j) := by
  induction j with
  | zero => decide
  | succ j ih =>
    calc
      (4+(j+1))^2 = ((4+j)+1)^2 := by rw [Nat.add_assoc]
      _ ≤ 2*(4+j)^2 := square_growth _ (by omega)
      _ ≤ 2*(2^(4+j)) := Nat.mul_le_mul_left _ ih
      _ = 2^(4+(j+1)) := by rw [← Nat.add_assoc,pow_succ,Nat.mul_comm]

theorem printed_search_has_successful_exponent (s : ℕ) : ∃ a,successfulSourceExponent s a := by
  let a := 64*(s+1)
  have a4 : 4≤a := by dsimp only [a]; omega
  have a2 : a^2 ≤ 2^a := by
    have rew : a=4+(a-4) := by omega
    have e := square_vs_power_two (a-4)
    rwa [← rew] at e
  have mOne : 1 ≤ (2:ℕ)^a := Nat.one_le_pow _ _ (by decide)
  have c : sourceC3 (2^a) ≤ 16*(2:ℕ)^a := by unfold sourceC3; omega
  have ceilBound : sourceH3 (2^a) ≤ 2*a+6 := by
    apply (Nat.clog_le_iff_le_pow (by decide : 1<(2:ℕ))).2
    calc
      4*sourceC3 (2^a)*2^a ≤ 4*(16*(2:ℕ)^a)*2^a :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 4 c)
      _ = 64*((2:ℕ)^a)^2 := by ring
      _ = 2^(2*a+6) := by
        rw [pow_add,Nat.mul_comm 2 a,pow_mul (2:ℕ) a 2]
        exact Nat.mul_comm _ _
  have bound : 16*sourceH3 (2^a)*s ≤ a^2 := by
    calc
      16*sourceH3 (2^a)*s = (16*s)*sourceH3 (2^a) := by ring
      _ ≤ (16*s)*(2*a+6) := Nat.mul_le_mul_left _ ceilBound
      _ ≤ (16*s)*(4*a) := Nat.mul_le_mul_left _ (by omega)
      _ = (64*s)*a := by ring
      _ ≤ a*a := Nat.mul_le_mul_right _ (by dsimp only [a]; omega)
      _ = a^2 := by ring
  refine ⟨a,?_⟩
  unfold successfulSourceExponent
  rw [printed_width_three_gamma]
  exact ⟨(show (16:ℕ)=2^4 by decide).le.trans (Nat.pow_le_pow_right (by decide) a4),
    bound.trans a2⟩

noncomputable def selectedSourceExponent (s : ℕ) := Nat.find (printed_search_has_successful_exponent s)

noncomputable def selectedSourceBase : ℕ→ℕ := fun s => 2^(selectedSourceExponent s)

theorem printed_source_selects_first_success (s : ℕ) :
    successfulSourceExponent s (selectedSourceExponent s) ∧
      ∀ a<selectedSourceExponent s, ¬successfulSourceExponent s a :=
  ⟨Nat.find_spec (printed_search_has_successful_exponent s),
    fun _ h => Nat.find_min (printed_search_has_successful_exponent s) h⟩

theorem printed_selected_threshold_at_least_sixteen (s : ℕ) : 16≤selectedSourceBase s := by
  exact (printed_source_selects_first_success s).1.1

#print axioms source_lambda_at_least_five
#print axioms source_nu_at_least_three
#print axioms sourceS_is_exact_largest_index
#print axioms large_source_index_gate
#print axioms large_source_enters_sparsifier
#print axioms printed_width_three_gamma
#print axioms printed_candidate_is_exact_rational_comparison
#print axioms printed_search_has_successful_exponent
#print axioms printed_source_selects_first_success
#print axioms printed_selected_threshold_at_least_sixteen
end F5R63.Sparsify