import S6Iterators
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Order.Floor.Semiring

namespace Section6

open scoped BigOperators
open Filter

noncomputable section

def lg (x : ℝ) := Real.log x / Real.log 2
def L (n : ℕ) : ℝ := Real.log n
def l (n : ℕ) : ℝ := Real.log (L n)
def beta (n : ℕ) : ℝ := l n / √(L n)
def alpha (n : ℕ) : ℝ := l n * beta n

lemma logTwo_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
lemma logTwo_le_one : Real.log 2 ≤ 1 := by
  convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1 <;> norm_num

lemma le_lg_of_two_pow_le (j T : ℕ) (h : 2 ^ j ≤ T) : (j : ℝ) ≤ lg T := by
  have hc : (2 : ℝ)^j ≤ T := by exact_mod_cast h
  have hl := Real.log_le_log (by positivity) hc
  rw [Real.log_pow] at hl
  exact (le_div_iff₀ logTwo_pos).mpr hl

lemma choose_log_lower (n j T : ℕ) (hj : 0 < j) (hj2 : 2*j ≤ n)
    (hT : n.choose j ≤ T) :
    (j : ℝ) * Real.log ((n : ℝ)/(2*j)) ≤ Real.log T := by
  have hp : (0 : ℝ) < j := by exact_mod_cast hj
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hhalf : (n : ℝ)/2 ≤ (n+1-j : ℕ) := by
    have hb : n ≤ 2*(n+1-j) := by omega
    have hc : (n : ℝ) ≤ 2*((n+1-j : ℕ) : ℝ) := by exact_mod_cast hb
    linarith
  have hpw : ((n : ℝ)/(2*j))^j ≤ (n.choose j : ℝ) := by
    calc
      _ = ((n : ℝ)/2)^j / (j : ℝ)^j := by rw [← div_pow]; congr 1; ring
      _ ≤ (((n+1-j : ℕ) : ℝ)^j) / (j : ℝ)^j :=
        div_le_div_of_nonneg_right (pow_le_pow_left₀ (by positivity) hhalf _) (by positivity)
      _ ≤ (((n+1-j : ℕ) : ℝ)^j) / (j.factorial : ℝ) := by
        apply div_le_div_of_nonneg_left (by positivity)
        · exact_mod_cast Nat.factorial_pos j
        · exact_mod_cast Nat.factorial_le_pow j
      _ ≤ _ := Nat.pow_le_choose j n
  have hTc : (n.choose j : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hs := Real.log_le_log (show 0 < ((n : ℝ)/(2*j))^j by positivity)
    (hpw.trans hTc)
  simpa only [Real.log_pow] using hs

/-- Finite optimizer. The two explicit scale comparisons are eventual elementary
inequalities in n alone. The measurement premise is supplied by F.A3. -/
theorem optimize_visits (n r Q R q T : ℕ) (κ K : ℝ)
    (hκ : 0 < κ) (_hK : 0 < K) (hn : 0 < n) (hr : 2 ≤ r) (hR : 0 < R) (hQR : R < Q)
    (hL : 0 < L n) (hl : 1 ≤ l n)
    (_hKQ : 256 ≤ K * l n)
    (hlog : (Q : ℝ) * Real.log r ≤ L n)
    (hsize : (n : ℝ) * alpha n ≥ 1)
    (hs₁ : alpha n ≤ 1) (hs₂ : 2 * K * l n * alpha n ≤ κ) (hs₃ : 32 * alpha n ≤ κ)
    (hs₄ : alpha n ≤ Real.exp (-(l n / 4)))
    (hs₅ : alpha n ≤ (Real.exp (-16) / 16) * Real.exp (-(l n / 8)))
    (hs₆ : 2 ≤ (min κ 1 / 512) * n * beta n)
    (hq : κ * (n : ℝ) * R / Q < (q : ℝ) + 1)
    (hgroup : (n : ℝ) ≤ r * lg T)
    (htaylor : 2 ^ min q n ≤ T)
    (hchoose : ∀ j ≤ q, n.choose j ≤ T)
    (hdiag : (K * l n < Q) → 16 * R ≤ Q →
      (Real.exp (-16) / 16) * n * Real.exp (-(64 * (R : ℝ)^2 / Q)) ≤ lg T) :
    (min κ 1 / 4096) * (n : ℝ) * alpha n ≤ lg T := by
  let δ := min κ 1 / 512
  have hδ : 0 < δ := div_pos (lt_min hκ zero_lt_one) (by norm_num)
  have hδκ : 512 * δ ≤ κ := by
    dsimp [δ]
    linarith [min_le_left κ 1]
  have hδ1 : 512 * δ ≤ 1 := by
    dsimp [δ]
    linarith [min_le_right κ 1]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hl0 : 0 < l n := by linarith
  have hβ : 0 < beta n := div_pos hl0 (Real.sqrt_pos.mpr hL)
  have hα : 0 < alpha n := mul_pos hl0 hβ
  have ht := le_lg_of_two_pow_le _ _ htaylor
  have hsmall (h : (n : ℝ) * alpha n ≤ q) : (n : ℝ) * alpha n ≤ lg T := by
    apply le_trans _ ht
    rw [Nat.cast_min]
    exact le_min h (by nlinarith [mul_nonneg (sub_nonneg.mpr hs₁) hn0.le])
  by_cases hfast : (n : ℝ) * alpha n ≤ lg T
  · calc
      _ = δ / 8 * ((n : ℝ) * alpha n) := by unfold δ; ring
      _ ≤ 1 * ((n : ℝ) * alpha n) := by gcongr <;> linarith
      _ ≤ _ := by simpa using hfast
  push_neg at hfast
  have hf : ¬ (n : ℝ) * alpha n ≤ q := fun he => (not_le.mpr hfast) (hsmall he)
  have hq2 : (q : ℝ) + 1 < 2 * ((n : ℝ) * alpha n) := by
    push_neg at hf
    linarith
  have hαR : 2 * alpha n * Q > κ * R := by
    have hh := (div_lt_iff₀ hQ0).mp (hq.trans hq2)
    apply (mul_lt_mul_iff_right₀ hn0).mp
    nlinarith only [hh]
  have hQl : K * l n < Q := by
    by_contra! h
    have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast hR
    nlinarith only [hαR, hs₂, mul_le_mul_of_nonneg_left h (show 0 ≤ 2 * alpha n by positivity),
      mul_le_mul_of_nonneg_left hR1 hκ.le]
  have hRQ : 16 * R ≤ Q := by
    by_contra! h
    have h' : (Q : ℝ) < 16 * (R : ℝ) := by exact_mod_cast h
    nlinarith only [hαR, mul_le_mul_of_nonneg_right hs₃ hQ0.le,
      mul_lt_mul_of_pos_left h' hκ]
  have hrs : 1 / alpha n < (r : ℝ) := by
    have hh := lt_of_le_of_lt hgroup (mul_lt_mul_of_pos_left hfast hr0)
    have hh' : 1 < (r : ℝ) * alpha n := by
      apply (mul_lt_mul_iff_right₀ hn0).mp
      linarith
    apply (div_lt_iff₀ hα).mpr
    exact hh'
  have hrl : l n / 4 ≤ Real.log r := by
    have hh := (one_div_le_one_div_of_le hα hs₄).trans hrs.le
    rw [one_div, Real.exp_neg, inv_inv] at hh
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hh
  have hQupper : (Q : ℝ) * l n ≤ 4 * L n := by
    nlinarith only [hlog, mul_le_mul_of_nonneg_left hrl hQ0.le]
  have hspec := (hdiag hQl hRQ).trans_lt hfast
  have hExp : Real.exp (-(64 * (R : ℝ)^2 / Q)) ≤ Real.exp (-(l n / 8)) := by
    let a := Real.exp (-16) / 16
    have ha : 0 < a := by unfold a; positivity
    apply (mul_le_mul_iff_right₀ (mul_pos ha hn0)).mp
    calc
      _ ≤ (n : ℝ) * alpha n := by
        dsimp [a]
        linarith
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hs₅ hn0.le
        dsimp [a]
        linarith
  have hqR : l n * Q ≤ 512 * (R : ℝ)^2 := by
    have hh := Real.exp_le_exp.mp hExp
    have h' : l n / 8 ≤ 64 * (R : ℝ)^2 / Q := by linarith
    nlinarith only [(le_div_iff₀ hQ0).mp h']
  have hβR : beta n * Q ≤ 64 * (R : ℝ) := by
    have hroot : 0 < √(L n) := Real.sqrt_pos.mpr hL
    have hsq : (l n * Q)^2 ≤ (64 * (R : ℝ) * √(L n))^2 := by
      calc
        _ ≤ (4 * L n) * (512 * (R : ℝ)^2) := by
          nlinarith only [mul_le_mul hQupper hqR (show 0 ≤ l n * Q by positivity)
            (show 0 ≤ 4 * L n by positivity)]
        _ ≤ _ := by
          rw [mul_pow, Real.sq_sqrt hL.le]
          nlinarith only [mul_nonneg hL.le (sq_nonneg (R : ℝ))]
    have hn' : 0 ≤ 64 * (R : ℝ) * √(L n) := by positivity
    have hle : l n * Q ≤ 64 * (R : ℝ) * √(L n) := by
      by_contra! hh
      nlinarith only [hsq, mul_pos (sub_pos.mpr hh)
        (show 0 < l n * Q + 64 * (R : ℝ) * √(L n) by positivity)]
    unfold beta
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hroot).mpr hle
  let j := ⌊δ * n * beta n⌋₊
  have hδn : 2 ≤ δ * (n : ℝ) * beta n := hs₆
  have hj₀ : (δ * (n : ℝ) * beta n) / 2 ≤ j := by
    have hlt := Nat.lt_floor_add_one (δ * (n : ℝ) * beta n)
    dsimp [j]
    linarith
  have hj₁ : (j : ℝ) ≤ δ * n * beta n := Nat.floor_le (by positivity)
  have hjpos : 0 < j := by exact_mod_cast (show (0 : ℝ) < j by linarith)
  have hjq : j ≤ q := by
    have hmul : δ * (n : ℝ) * beta n * Q ≤ κ * n * R := by
      have h₁ := mul_le_mul_of_nonneg_left hβR (show 0 ≤ δ * (n : ℝ) by positivity)
      have h₂ := mul_le_mul_of_nonneg_right hδκ (show 0 ≤ (n : ℝ) * R by positivity)
      have h₃ := mul_nonneg (show 0 ≤ δ by positivity) (show 0 ≤ (n : ℝ) * R by positivity)
      nlinarith only [h₁, h₂, h₃]
    have hjlt : (j : ℝ) < (q : ℝ) + 1 := hj₁.trans_lt
      (((le_div_iff₀ hQ0).mpr hmul).trans_lt hq)
    have hh : j < q + 1 := by exact_mod_cast hjlt
    omega
  have hjexp : 2 * (j : ℝ) ≤ (n : ℝ) * Real.exp (-(l n / 4)) := by
    have h₁ : 2 * δ ≤ l n := by linarith
    have h₂ := mul_le_mul_of_nonneg_right h₁ (show 0 ≤ (n : ℝ) * beta n by positivity)
    have h₃ := mul_le_mul_of_nonneg_left hs₄ hn0.le
    unfold alpha at h₃
    nlinarith only [hj₁, h₂, h₃]
  have hjn : 2 * j ≤ n := by
    have h := Real.exp_le_one_iff.mpr (show -(l n / 4) ≤ 0 by linarith)
    have hh := hjexp.trans (by simpa using mul_le_mul_of_nonneg_left h hn0.le)
    exact_mod_cast hh
  have hentropy : l n / 4 ≤ Real.log ((n : ℝ)/(2*j)) := by
    have hjp : (0 : ℝ) < j := by exact_mod_cast hjpos
    have hb : Real.exp (l n / 4) ≤ (n : ℝ)/(2*j) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * (j : ℝ))).mpr
      rw [Real.exp_neg] at hjexp
      have he := (le_div_iff₀ (Real.exp_pos (l n / 4))).mp (by simpa [div_eq_mul_inv] using hjexp)
      nlinarith only [he]
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hb
  have hlT := choose_log_lower n j T hjpos hjn (hchoose j hjq)
  have hlc := mul_le_mul hj₀ hentropy (by linarith : 0 ≤ l n / 4)
    (show 0 ≤ (j : ℝ) by positivity)
  have hh : δ / 8 * ((n : ℝ) * alpha n) ≤ Real.log T := by
    unfold alpha
    linarith only [hlc, hlT]
  have hh' : δ / 8 * ((n : ℝ) * alpha n) ≤ lg T := by
    apply (le_div_iff₀ logTwo_pos).mpr
    have hh0 : 0 ≤ δ / 8 * ((n : ℝ) * alpha n) := by positivity
    exact (mul_le_mul_of_nonneg_left logTwo_le_one hh0).trans (by simpa using hh)
  convert hh' using 1 <;> unfold δ <;> ring

#print axioms choose_log_lower
#print axioms optimize_visits

end
end Section6



