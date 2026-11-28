import J4R43LiteralOutsideRootGuards
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Literal root schedule separation: the true outside enumeration
exponent M/L is little-o of M/sqrt(log s), before claiming any
arithmetic speed-up for a different, nonzero probe. -/
namespace J4R43LiteralOutside
open scoped Topology
open Filter J1PPrinted
noncomputable section
set_option linter.unusedSimpArgs false

def printedRootQ (s : ℕ) : ℕ := Nat.clog 2 s/epsDen

theorem printed_q_grows : Tendsto printedRootQ atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop ((2:ℕ)^(n*epsDen)+1)] with s h
  unfold printedRootQ
  apply (Nat.le_div_iff_mul_le (by norm_num [epsDen] : 0<epsDen)).mpr
  exact ((Nat.lt_clog_iff_pow_lt (by decide : 1<2)).mpr (by omega)).le

theorem printed_log_group (s : ℕ) :
    Nat.clog 2 s≤epsDen*(printedRootQ s+1) := by
  let l := Nat.clog 2 s
  have pos : 0<epsDen := by norm_num [epsDen]
  have h := Nat.div_add_mod l epsDen
  have b := Nat.mod_lt l pos
  change l≤epsDen*(l/epsDen+1)
  rw [Nat.mul_add,mul_one]
  omega

theorem sqrt_log_on_printed_words (s : ℕ) (h : 1≤s) :
    Real.sqrt (Real.log (s:ℝ))≤((epsDen:ℝ)+1)*((2:ℝ)^printedRootQ s) := by
  let l := Nat.clog 2 s
  let q := printedRootQ s
  have sn : 0<(s:ℝ) := by exact_mod_cast (show 0<s by omega)
  have pw : (s:ℝ)≤(2:ℝ)^l := by
    exact_mod_cast (Nat.clog_le_iff_le_pow (by decide : 1<2)).mp (show Nat.clog 2 s≤l from le_rfl)
  have lp := Real.log_le_log sn pw
  rw [Real.log_pow] at lp
  have log2 : Real.log 2≤1 := by
    have e := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at e
    exact e
  have upper : Real.log (s:ℝ)≤(l:ℝ) := lp.trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left log2 (Nat.cast_nonneg l))
  have root := Real.sqrt_le_sqrt upper
  have sqrt_le : Real.sqrt (l:ℝ)≤(l:ℝ)+1 := by
    have n : (0:ℝ)≤l := Nat.cast_nonneg l
    have k : (0:ℝ)≤(l:ℝ)+1 := by positivity
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) k).mp
    rw [Real.sq_sqrt n]
    nlinarith only [n,sq_nonneg (l:ℝ)]
  have lBound : (l:ℝ)≤(epsDen:ℝ)*((q:ℝ)+1) := by
    exact_mod_cast printed_log_group s
  have qBound : (q:ℝ)+1≤(2:ℝ)^q := by
    exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n:=q))
  calc
    _ ≤ (l:ℝ)+1 := root.trans sqrt_le
    _ ≤ ((epsDen:ℝ)+1)*((q:ℝ)+1) := by nlinarith [Nat.cast_nonneg (α:=ℝ) q]
    _ ≤ _ := mul_le_mul_of_nonneg_left qBound (by positivity)

theorem outside_exponent_strictly_smaller :
    Tendsto (fun s : ℕ=>Real.sqrt (Real.log (s:ℝ))/((2:ℝ)^stepA (Nat.clog 2 s) 0)) atTop (𝓝 0) := by
  have geo : Tendsto (fun n : ℕ=>((1/2:ℝ)^n)) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have major := (geo.comp printed_q_grows).const_mul ((epsDen:ℝ)+1)
  rw [mul_zero] at major
  apply squeeze_zero' (Eventually.of_forall (fun s=>div_nonneg (Real.sqrt_nonneg _) (by positivity))) _ major
  filter_upwards [eventually_ge_atTop (1:ℕ)] with s pos
  let q := printedRootQ s
  have grid : stepA (Nat.clog 2 s) 0=2*q := by simp [stepA,stepU,q,printedRootQ]
  change Real.sqrt (Real.log (s:ℝ))/((2:ℝ)^stepA (Nat.clog 2 s) 0)≤((epsDen:ℝ)+1)*((1/2:ℝ)^q)
  rw [grid,mul_comm 2 q,pow_mul,pow_two]
  have gp : (0:ℝ)<(2:ℝ)^q := by positivity
  rw [div_pow,one_pow]
  have upper := sqrt_log_on_printed_words s pos
  change Real.sqrt (Real.log (s:ℝ))≤((epsDen:ℝ)+1)*((2:ℝ)^q) at upper
  field_simp [gp.ne']
  nlinarith

#print axioms printed_q_grows
#print axioms printed_log_group
#print axioms sqrt_log_on_printed_words
#print axioms outside_exponent_strictly_smaller
end
end J4R43LiteralOutside

