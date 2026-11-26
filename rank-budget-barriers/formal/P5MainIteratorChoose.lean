import P5MainIteratorTrace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Bounds

/-! Finite logarithmic consequences of the printed obligations. The
entropy-scale lower bound uses the exact finite binomial bound, prior to
accounting for any Taylor coefficient arithmetic. -/
namespace P5MainIterator
open scoped BigOperators Classical

theorem binomial_ge_power_ratio (n j : ℕ) (hj : j≤n) :
    ((n:ℝ)/(j:ℝ))^j ≤ (n.choose j : ℝ) := by
  induction j generalizing n with
  | zero => simp
  | succ k ih =>
    cases n with
    | zero => omega
    | succ m =>
      cases k with
      | zero => simp
      | succ k =>
        have hkm : k+1≤m := by omega
        have hratio :
            (↑(m+1):ℝ)/↑(k+2) ≤ (m:ℝ)/↑(k+1) := by
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          push_cast
          have hR : (k:ℝ)+1≤(m:ℝ) := by exact_mod_cast hkm
          nlinarith
        have hfirst : 0≤(↑(m+1):ℝ)/↑(k+2) := by positivity
        have hc : (m:ℝ)+1 > 0 := by positivity
        have hd : (k:ℝ)+2 > 0 := by positivity
        have hs : (↑(m+1):ℝ) * (m.choose (k+1):ℝ) =
            (Nat.choose (m+1) (k+2):ℝ)*↑(k+2) := by
          exact_mod_cast Nat.succ_mul_choose_eq m (k+1)
        calc
          _ = ((↑(m+1):ℝ)/↑(k+2))^(k+1) * ((↑(m+1):ℝ)/↑(k+2)) := by rw [pow_succ]
          _ ≤ (m.choose (k+1):ℝ) * ((↑(m+1):ℝ)/↑(k+2)) :=
            mul_le_mul_of_nonneg_right ((pow_le_pow_left₀ hfirst hratio _).trans (ih m hkm)) hfirst
          _ = _ := by
            rw [←mul_div_assoc, mul_comm _ (↑(m+1):ℝ),hs]
            field_simp

noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

theorem binary_exponent_le (T k : ℕ) (hk : 2^k≤T) :
    (k:ℝ) ≤ logTwo T := by
  apply (le_div_iff₀ (Real.log_pos (by norm_num))).mpr
  have h : (2:ℝ)^k ≤ (T:ℝ) := by exact_mod_cast hk
  have hh := Real.log_le_log (show 0<(2:ℝ)^k from by positivity) h
  rwa [Real.log_pow] at hh

theorem paid_taylor_entropy {V : Type*} [Fintype V] [DecidableEq V]
    (q j T : ℕ) (hj : 0<j) (hq : j≤q) (hn : j≤Fintype.card V)
    (ht : (TaylorList V q).card≤T) :
    (j:ℝ) * logTwo ((Fintype.card V:ℝ)/(j:ℝ)) ≤ logTwo T := by
  have hbe := binomial_ge_power_ratio (Fintype.card V) j hn
  have hct : (Fintype.card V).choose j ≤ T := by
    have hpow : 1 ≤ 2^j := Nat.succ_le_of_lt (Nat.pow_pos (by decide))
    have hmul := Nat.mul_le_mul_right ((Fintype.card V).choose j) hpow
    rw [one_mul] at hmul
    exact hmul.trans ((choose_le_taylorList q j hq).trans ht)
  have hle : ((Fintype.card V:ℝ)/(j:ℝ))^j ≤ (T:ℝ) := hbe.trans (by exact_mod_cast hct)
  have hpos : (0:ℝ)<(Fintype.card V:ℝ)/(j:ℝ) := by
    apply div_pos <;> exact_mod_cast (by omega : 0<_)
  have hh := Real.log_le_log (pow_pos hpos _) hle
  rw [Real.log_pow] at hh
  unfold logTwo
  rw [←mul_div_assoc]
  exact div_le_div_of_nonneg_right hh (Real.log_nonneg (by norm_num))

theorem small_alphabet_branch (n r s T : ℕ) (α : ℝ)
    (hgroup : n≤r*s) (hpay : 2^s≤T) (ha : 0≤α) (hr : r*α≤1) :
    (n:ℝ)*α≤logTwo T := by
  have hgroup' : (n:ℝ) ≤ r*s := by exact_mod_cast hgroup
  have h := mul_le_mul_of_nonneg_right hgroup' ha
  apply h.trans
  rw [mul_right_comm]
  calc
    (↑r * α) * (s:ℝ) ≤ 1 * (s:ℝ) := mul_le_mul_of_nonneg_right hr (by positivity)
    _ = (s:ℝ) := one_mul _
    _ ≤ _ := binary_exponent_le T s hpay

#print axioms binomial_ge_power_ratio
#print axioms binary_exponent_le
#print axioms paid_taylor_entropy
#print axioms small_alphabet_branch
end P5MainIterator
