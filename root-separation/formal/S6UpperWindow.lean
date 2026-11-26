import S6UpperTail
import S6Upper
import S6Tune

namespace Section6

open Finset
open scoped BigOperators
set_option linter.unusedSectionVars false

noncomputable section

variable {A I : Type*} [Fintype A] [LinearOrder A] [Fintype I] [DecidableEq I]

def spectralP (r : ℕ) : ℝ := ((r : ℝ)-1)/(2*r)

lemma spectralP_bounds {r : ℕ} (hr : 2 ≤ r) : 1/4 ≤ spectralP r ∧ spectralP r ≤ 1/2 := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hp : 0 < (2 : ℝ)*r := by linarith
  unfold spectralP
  constructor
  · apply (le_div_iff₀ hp).mpr
    linarith
  · apply (div_le_iff₀ hp).mpr
    linarith

/-- The exact row fraction of the literal tensor swap matrix, before making copies. -/
theorem row_fraction_binomial (hr : 2 ≤ Fintype.card A) (window : Finset ℕ) :
    (Fintype.card (Exceptional I A window) : ℝ) / cubeSize I A =
      ∑ j ∈ (range (Fintype.card I + 1)).filter (· ∉ window),
        binMass (Fintype.card I) (spectralP (Fintype.card A)) j := by
  let r := Fintype.card A
  let Q := Fintype.card I
  let a := (negativePairs A).card
  let b := (nonnegativePairs A).card
  have hpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have ⟨hcount, hsum⟩ := single_pair_counts (A := A)
  have hcount' : 2 * (a : ℝ) + r = (r : ℝ)^2 := by exact_mod_cast hcount
  have hsum' : (a : ℝ) + b = (r : ℝ)^2 := by exact_mod_cast hsum
  have hpa : spectralP r = (a : ℝ) / (r : ℝ)^2 := by
    unfold spectralP
    field_simp [hpos.ne']
    nlinarith only [hcount', congrArg (fun x : ℝ => x * r) hcount']
  have hpb : 1 - spectralP r = (b : ℝ) / (r : ℝ)^2 := by
    rw [hpa]
    field_simp [hpos.ne']
    linarith only [hsum']
  rw [exceptional_row_count, Nat.cast_sum, sum_div]
  apply sum_congr rfl
  intro j hj
  change ((Q.choose j * a^j * b^(Q-j) : ℕ) : ℝ) / cubeSize I A = binMass Q (spectralP r) j
  have hjQ : j ≤ Q := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hj).1)
  have hD : (cubeSize I A : ℝ) = ((r : ℝ)^2)^Q := by simp [r, Q, pow_two]
  unfold binMass
  rw [hD, hpb, hpa, div_pow, div_pow]
  push_cast
  have he : ((a : ℝ)^j / ((r : ℝ)^2)^j) * ((b : ℝ)^(Q-j) / ((r : ℝ)^2)^(Q-j)) =
      ((a : ℝ)^j * (b : ℝ)^(Q-j)) / ((r : ℝ)^2)^Q := by
    rw [div_mul_div_comm, ← pow_add, Nat.add_sub_cancel' hjQ]
  conv_rhs => rw [mul_assoc, he]
  ring

def centeredStart (Q R r : ℕ) : ℕ :=
  ⌊(Q : ℝ) * spectralP r - ((R : ℝ)-1)/2⌋₊

def centeredWindow (Q R r : ℕ) : Finset ℕ := Ico (centeredStart Q R r) (centeredStart Q R r + R)

lemma centeredWindow_card (Q R r : ℕ) : (centeredWindow Q R r).card = R := by
  simp [centeredWindow]

lemma centeredWindow_ends {Q R r : ℕ} (hr : 2 ≤ r) (hQR : 6*R ≤ Q) :
    centeredStart Q R r + R ≤ Q + 1 := by
  obtain ⟨hlo,hhi⟩ := spectralP_bounds hr
  have hQR' : (6 : ℝ)*R ≤ Q := by exact_mod_cast hQR
  have hq := mul_le_mul_of_nonneg_left hlo (show 0 ≤ (Q : ℝ) by positivity)
  have hq' := mul_le_mul_of_nonneg_left hhi (show 0 ≤ (Q : ℝ) by positivity)
  have hs := Nat.floor_le (show 0 ≤ (Q : ℝ)*spectralP r - ((R : ℝ)-1)/2 by linarith)
  have he : (centeredStart Q R r : ℝ) + R ≤ (Q : ℝ) + 1 := by
    unfold centeredStart
    linarith only [hs, hq', hQR']
  exact_mod_cast he

lemma centeredWindow_contains {Q R r j : ℕ} (hr : 2 ≤ r) (hR : 32 ≤ R)
    (hQR : 6*R ≤ Q) (hj : |(j : ℝ)-(Q : ℝ)*spectralP r| < (R : ℝ)/4) :
    j ∈ centeredWindow Q R r := by
  obtain ⟨hlo,_⟩ := spectralP_bounds hr
  have hQR' : (6 : ℝ)*R ≤ Q := by exact_mod_cast hQR
  have hR' : (32 : ℝ) ≤ R := by exact_mod_cast hR
  have hq := mul_le_mul_of_nonneg_left hlo (show 0 ≤ (Q : ℝ) by positivity)
  let x := (Q : ℝ)*spectralP r - ((R : ℝ)-1)/2
  have hx : 0 ≤ x := by unfold x; linarith only [hq, hQR', hR']
  have hs := Nat.floor_le hx
  have hs' := Nat.lt_floor_add_one x
  obtain ⟨h₁,h₂⟩ := abs_lt.mp hj
  have hj1 : (⌊x⌋₊ : ℝ) ≤ j := by
    unfold x at hs
    linarith only [hs,h₁,hR']
  have hj2 : (j : ℝ) < (⌊x⌋₊ : ℝ) + R := by
    unfold x at hs'
    linarith only [hs',h₂,hR']
  exact mem_Ico.mpr ⟨by exact_mod_cast hj1, by exact_mod_cast hj2⟩

theorem centered_row_tail (hr : 2 ≤ Fintype.card A) {R : ℕ}
    (hR : 32 ≤ R) (hQR : 6*R ≤ Fintype.card I) :
    (Fintype.card (Exceptional I A (centeredWindow (Fintype.card I) R (Fintype.card A))) : ℝ) /
      cubeSize I A ≤ 2 * Real.exp (-((R : ℝ)^2 / (64 * Fintype.card I))) := by
  rw [row_fraction_binomial hr]
  have hp := spectralP_bounds hr
  have hQ : 0 < Fintype.card I := by omega
  have hQR' : (6 : ℝ)*R ≤ Fintype.card I := by exact_mod_cast hQR
  have ht := bin_window_upper (Fintype.card I) (spectralP (Fintype.card A)) ((R : ℝ)/4)
    (centeredWindow (Fintype.card I) R (Fintype.card A)) hQ (by linarith only [hp.1])
    (by linarith only [hp.2]) (by positivity) (by linarith only [hQR', show (0 : ℝ) ≤ R by positivity])
    (fun j _ hj => le_of_not_gt fun ht => hj (centeredWindow_contains hr hR hQR ht))
  convert ht using 3 <;> ring

/-- The published parameter inequalities leave enough margin even with
the elementary weaker tail exp(-R²/(64Q)) proved above. -/
theorem source_tail_budget (lam nu r Q R b β : ℕ)
    (hlam : 0 < lam) (hnu : 1 ≤ nu) (hr : 0 < r) (hQ : 0 < Q) (hb : 0 < b)
    (hlg : lg lam ≤ nu) (hr2 : r^2 ≤ lam) (hQL : Q*128*nu ≤ lam)
    (hRL : (β+3)^2 * lam ≤ R^2) (hbl : b ≤ lam^β) :
    2 * Real.exp (-((R : ℝ)^2 / (64*Q))) ≤ 1/((b : ℝ)*r^2*lam) := by
  have hν : (1 : ℝ) ≤ nu := by exact_mod_cast hnu
  have hΛ : (0 : ℝ) < lam := by exact_mod_cast hlam
  have hq : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hrp : (0 : ℝ) < r := by exact_mod_cast hr
  have hbp : (0 : ℝ) < b := by exact_mod_cast hb
  have hlg' := (div_le_iff₀ logTwo_pos).mp hlg
  have hloglam : Real.log lam ≤ nu := by
    exact hlg'.trans (by simpa using mul_le_mul_of_nonneg_left logTwo_le_one (show 0 ≤ (nu : ℝ) by positivity))
  have hler : Real.log ((r : ℝ)^2) ≤ Real.log lam :=
    Real.log_le_log (pow_pos hrp _) (by exact_mod_cast hr2)
  have hleb : Real.log b ≤ β * Real.log lam := by
    simpa only [Real.log_pow] using Real.log_le_log hbp (by exact_mod_cast hbl : (b : ℝ) ≤ (lam : ℝ)^β)
  have hQL' : (Q : ℝ)*128*nu ≤ lam := by exact_mod_cast hQL
  have hRL' : ((β : ℝ)+3)^2 * lam ≤ (R : ℝ)^2 := by exact_mod_cast hRL
  have hrat : 2*((β : ℝ)+3)^2*nu ≤ (R : ℝ)^2 / (64*Q) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hRL', mul_le_mul_of_nonneg_left hQL' (sq_nonneg ((β : ℝ)+3))]
  have hnineq : 1 + ((β : ℝ)+2)*nu ≤ 2*((β : ℝ)+3)^2*nu := by
    have hb0 : (0 : ℝ) ≤ β := by positivity
    have h0 : (1 : ℝ) + ((β : ℝ)+2) ≤ 2*((β : ℝ)+3)^2 := by nlinarith only [hb0,sq_nonneg (β : ℝ)]
    nlinarith only [mul_le_mul_of_nonneg_right h0 (show (0 : ℝ) ≤ nu by positivity), hν]
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp,
    Real.log_div (by norm_num) (by positivity), Real.log_one, zero_sub,
    Real.log_mul (by positivity) hΛ.ne', Real.log_mul hbp.ne' (pow_pos hrp _).ne']
  nlinarith only [logTwo_le_one, hrat, hnineq, hler, hleb, hloglam,
    mul_le_mul_of_nonneg_left hloglam (show (0 : ℝ) ≤ β by positivity)]

#print axioms row_fraction_binomial
#print axioms centeredWindow_ends
#print axioms centeredWindow_contains
#print axioms centered_row_tail
#print axioms source_tail_budget

end
end Section6






