import P5FrontendG1TannerSchedule

/-! The printed width-two schedule is eventually genuinely in the q_G>1
case, and B is unbounded. This consists of deterministic integer
arithmetic and does not require an expander existence theorem. -/
namespace Paper5.FrontendG1.Tanner
open Paper5.NativeEntry

def polyCap : ℕ := 320000*258^2*3^3

private theorem quintic_step {j : ℕ} (hj : 16≤j) : (j+1)^5≤2*j^5 := by
  have h0 : 16*(j+1)≤17*j := by omega
  have h1 := Nat.pow_le_pow_left h0 5
  simp only [mul_pow] at h1
  apply Nat.le_of_mul_le_mul_left _ (by decide : 0<(16:ℕ)^5)
  calc
    _ ≤ (17:ℕ)^5*j^5 := h1
    _ ≤ _ := by
      rw [←mul_assoc]
      exact Nat.mul_le_mul_right _ (by decide)

theorem capped_quintic_dyadic {a : ℕ} (ha : 128≤a) : polyCap*a^5≤2^(a-1) := by
  induction a,ha using Nat.le_induction with
  | base => decide
  | succ a ha ih =>
    calc
      _ ≤ polyCap*(2*a^5) := Nat.mul_le_mul_left _ (quintic_step (by omega))
      _ = 2*(polyCap*a^5) := by ring
      _ ≤ 2*2^(a-1) := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [show a+1-1=(a-1)+1 by omega,pow_succ']

theorem printed_source_D_below_m {n m : ℕ} (ha : 128≤sourceLambda n)
    (hnm : n≤m) (hmn : m≤2*n) (hs : 2≤printedGroups n) :
    sourceD (sparB₂ (printedGroups n) hs) m<m := by
  let a := sourceLambda n
  let B := sparB₂ (printedGroups n) hs
  have hp : m≤2^(a+1) := by
    rw [pow_succ']
    exact hmn.trans (Nat.mul_le_mul_left 2 (Nat.le_pow_clog (by decide) n))
  have hlog := Nat.log_mono_right (b:=2) hp
  rw [Nat.log_pow (by decide)] at hlog
  have hmu : sourceMu m≤3*a := by
    unfold sourceMu
    omega
  have hB : B≤258*a := (literal_unit_source_B_bound hs).2
  have hBound : sourceD B m≤polyCap*a^5 := by
    unfold sourceD
    calc
      _ ≤ 320000*(258*a)^2*(3*a)^3 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hB 2))
          (Nat.pow_le_pow_left hmu 3)
      _ = _ := by unfold polyCap; ring
  have hlow : (2:ℕ)^(a-1)<n :=
    (Nat.lt_clog_iff_pow_lt (by decide)).mp (by change a-1<a; omega)
  exact (hBound.trans (capped_quintic_dyadic ha)).trans_lt (hlow.trans_le hnm)

theorem eventually_printed_groups_unbounded (K : ℕ) :
    ∃ n₀ : ℕ,∀ n≥n₀,K≤printedGroups n := by
  let a₀ := max 128 (K^2)
  refine ⟨(2:ℕ)^(2^a₀),?_⟩
  intro n hn
  let j := sourceNu n
  have hL : (2:ℕ)^a₀≤sourceLambda n := by
    have hh := Nat.clog_mono_right 2 hn
    simpa only [Nat.clog_pow 2 _ (by decide),sourceLambda] using hh
  have hj : a₀≤j := by
    have hh := Nat.clog_mono_right 2 hL
    simpa only [Nat.clog_pow 2 _ (by decide),sourceNu,j] using hh
  have h128 : 128≤j := (le_max_left _ _).trans hj
  have hk2 : K^2≤j := (le_max_right _ _).trans hj
  have hy : K^2*j^4≤sourceLambda n := by
    calc
      _ ≤ j*j^4 := Nat.mul_le_mul_right _ hk2
      _ = j^5 := by ring
      _ ≤ polyCap*j^5 := by
        have hOne : 1≤polyCap := by decide
        simpa only [one_mul] using Nat.mul_le_mul_right (j^5) hOne
      _ ≤ 2^(j-1) := capped_quintic_dyadic h128
      _ ≤ _ := ((Nat.lt_clog_iff_pow_lt (by decide : 1<(2:ℕ))).mp (by
        change j-1<j
        omega)).le
  unfold printedGroups
  have hj0 : 0<j^2 := pow_pos (by omega) _
  apply (Nat.le_div_iff_mul_le hj0).mpr
  apply Nat.le_sqrt'.mpr
  exact (show (K*j^2)^2=K^2*j^4 by ring) ▸ hy

theorem printed_B_ge_s (s : ℕ) (hs : 2≤s) : s≤sparB₂ s hs := by
  have hh := (spar_first_success s hs).1.2
  have hM : 1*s≤4*(4+sparExponent s hs)*s :=
    Nat.mul_le_mul_right s (by omega)
  unfold sparB₂
  omega

/-- Simultaneously every requested lower bound on B and the q_G>1 guard,
at all large source sizes n with n≤m≤2n (in particular the guarded cubic
clause count 7N/2 at n=2N). -/
theorem actual_printed_large_tanner (K : ℕ) :
    ∃ n₀ : ℕ, ∀ n≥n₀,∀ m, n≤m → m≤2*n →
      ∃ hs : 2≤printedGroups n,
        K≤sparB₂ (printedGroups n) hs ∧
        1<sourceQ (sparB₂ (printedGroups n) hs) m := by
  obtain ⟨n₁,hN⟩ := eventually_printed_groups_unbounded (max 2 K)
  refine ⟨max n₁ (2^128),?_⟩
  intro n hn m hnm hmn
  have hb := hN n ((le_max_left _ _).trans hn)
  have hs : 2≤printedGroups n := (le_max_left _ _).trans hb
  refine ⟨hs,((le_max_right _ _).trans hb).trans (printed_B_ge_s _ hs),?_⟩
  have hn2 : (2:ℕ)^128≤n := (le_max_right _ _).trans hn
  have ha := Nat.clog_mono_right 2 hn2
  rw [Nat.clog_pow 2 _ (by decide)] at ha
  have hm : 0<m := by
    have ht : 0<(2:ℕ)^128 := by positivity
    omega
  exact source_q_gt_one_of_D_lt (literal_unit_source_B_bound hs).1 hm
    (printed_source_D_below_m ha hnm hmn hs)

#print axioms capped_quintic_dyadic
#print axioms printed_source_D_below_m
#print axioms eventually_printed_groups_unbounded
#print axioms printed_B_ge_s
#print axioms actual_printed_large_tanner
end Paper5.FrontendG1.Tanner