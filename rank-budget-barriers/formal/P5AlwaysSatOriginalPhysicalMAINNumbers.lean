import P5MainBalanceNodeGrowth
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Root feasibility at the literal variable count of (M.7), not at
4N from the old four-copy family. Both b+w=6 and b+w=7 fit the same mesh. -/
namespace Paper5.AlwaysSatOriginal.Physical
open P5MainBalance Filter Real
open scoped Classical

theorem mainLambda_as_clog (n : ℕ) : mainLambda n=Nat.clog 2 n := by
  have h := Real.natCeil_logb_natCast 2 n
  simpa only [mainLambda,P5MainIterator.logTwo,Real.logb] using h

theorem mainNu_as_clog (n : ℕ) : mainNu n=Nat.clog 2 (mainLambda n) := by
  have h := Real.natCeil_logb_natCast 2 (mainLambda n)
  simpa only [mainNu,P5MainIterator.logTwo,Real.logb] using h

noncomputable def mainCells (n : ℕ) : ℕ := (mainAlphabet n)^(2*mainNodes n)

theorem alphabet_squared_le (n : ℕ) : (mainAlphabet n)^2≤mainLambda n := by
  by_cases hν : mainNu n=0
  · simp [mainAlphabet,hν]
  · have hpos : 1≤(mainNu n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hν
    have hden : 1≤(mainNu n:ℝ)^2 := one_le_pow₀ hpos
    have h := (Nat.floor_le (div_nonneg (sqrt_nonneg _) (by positivity) :
      0≤sqrt (mainLambda n:ℝ)/(mainNu n:ℝ)^2)).trans
      (div_le_self (sqrt_nonneg _) hden)
    change (mainAlphabet n:ℝ)≤sqrt (mainLambda n:ℝ) at h
    have hh := pow_le_pow_left₀ (show 0≤(mainAlphabet n:ℝ) by positivity) h 2
    rw [sq_sqrt (by positivity)] at hh
    exact_mod_cast hh

theorem mainCells_squared (n : ℕ) : (mainCells n)^2≤(2:ℕ)^(mainLambda n/64) := by
  let lam := mainLambda n
  let ν := mainNu n
  let r := mainAlphabet n
  let Q := mainNodes n
  have hcap : r^2≤(2:ℕ)^ν := (alphabet_squared_le n).trans
    (by dsimp only [ν,lam]; rw [mainNu_as_clog]; exact Nat.le_pow_clog (by decide) _)
  have hmul : ν*(2*Q)*64≤lam := by
    rw [show ν*(2*Q)*64=Q*(128*ν) by ring]
    exact Nat.div_mul_le_self lam (128*ν)
  have hexp : ν*(2*Q)≤lam/64 := (Nat.le_div_iff_mul_le (by decide)).mpr hmul
  change (r^(2*Q))^2≤(2:ℕ)^(lam/64)
  calc
    _ = (r^2)^(2*Q) := by rw [←pow_mul,←pow_mul,Nat.mul_comm (2*Q) 2]
    _ ≤ ((2:ℕ)^ν)^(2*Q) := Nat.pow_le_pow_left hcap _
    _ = (2:ℕ)^(ν*(2*Q)) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hexp

private theorem squares_dyadic (x : ℕ) (hx : 8≤x) : 2*x^2≤(2:ℕ)^(x-1) := by
  induction x, hx using Nat.le_induction with
  | base => decide
  | succ x hx ih =>
    have h : 8*(x+1)≤9*x := by omega
    have hh := Nat.pow_le_pow_left h 2
    rw [mul_pow,mul_pow] at hh
    have hb : (x+1)^2≤2*x^2 := by
      apply Nat.le_of_mul_le_mul_left _ (by decide : 0<(8:ℕ)^2)
      exact hh.trans (show 9^2*x^2≤8^2*(2*x^2) by
        rw [←mul_assoc]; exact Nat.mul_le_mul_right _ (by decide))
    calc
      2*(x+1)^2 ≤ 2*(2*x^2) := Nat.mul_le_mul_left _ hb
      _ ≤ 2*((2:ℕ)^(x-1)) := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [show x+1-1=x-1+1 by omega,pow_succ']

theorem main_mesh_at_n (n : ℕ) (hl : 8≤mainLambda n) :
    16*(mainCells n)^2≤n ∧ 2*mainNodes n*(mainAlphabet n)^2≤n := by
  let lam := mainLambda n
  have hp : (2:ℕ)^(lam-1)<n := by
    apply (Nat.lt_clog_iff_pow_lt (by decide)).mp
    rw [←mainLambda_as_clog]
    omega
  refine ⟨?_,?_⟩
  · calc
      16*(mainCells n)^2 ≤ (2:ℕ)^4 * 2^(lam/64) :=
        Nat.mul_le_mul_left _ (mainCells_squared n)
      _ = (2:ℕ)^(4+lam/64) := (pow_add _ _ _).symm
      _ ≤ (2:ℕ)^(lam-1) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ _ := hp.le
  · calc
      _ ≤ 2*lam*lam := Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.div_le_self _ _)) (alphabet_squared_le n)
      _ = 2*lam^2 := by ring
      _ ≤ (2:ℕ)^(lam-1) := squares_dyadic lam hl
      _ ≤ _ := hp.le

theorem main_mesh_eventual :
    ∀ᶠ n : ℕ in atTop, 72≤mainAlphabet n ∧ 0<mainNodes n ∧
      16*(mainCells n)^2≤n ∧ 2*mainNodes n*(mainAlphabet n)^2≤n := by
  filter_upwards [printed_alphabet_eventually_large 72,printed_nodes_eventually_large 1,
    lambda_ge_along_sizes 8] with n hR hQ hl
  exact ⟨hR,hQ,main_mesh_at_n n (by exact_mod_cast hl)⟩

#print axioms mainLambda_as_clog
#print axioms mainNu_as_clog
#print axioms alphabet_squared_le
#print axioms mainCells_squared
#print axioms main_mesh_at_n
#print axioms main_mesh_eventual
end Paper5.AlwaysSatOriginal.Physical