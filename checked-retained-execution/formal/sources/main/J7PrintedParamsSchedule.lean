import J7PrintedParamsBridge
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Printed root parameter promises hold at an explicit source threshold. -/

namespace J7PrintedParams
noncomputable section
set_option maxHeartbeats 1600000

def sourceSize (N : ℕ) : ℕ := 4*N + (N + 3*N/2 + 4*N)

/-- The four-clone family has 4N variables, N pin clauses, 3N/2 graph
clauses, and 4N implication clauses. The original fixed-density size
parameter is s=n+m and is below the number of wires. -/
theorem source_size (N : ℕ) (even : N % 2 = 0) :
    2*sourceSize N = 21*N ∧ sourceSize N ≤ 24*N := by
  unfold sourceSize
  omega

def rootU (s : ℕ) : ℕ := Nat.clog 2 s / 131072
def rootT (s : ℕ) : ℕ := 2*rootU s - 1
def rootDelta (s : ℕ) : ℕ := Nat.ceil ((s:ℝ)^(9/10:ℝ))

private theorem dyadic_rpow (k : ℕ) :
    ((2^(10*k) : ℕ) : ℝ)^(9/10:ℝ) = ((2^(9*k) : ℕ) : ℝ) := by
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  have h : ((10*k : ℕ):ℝ)*(9/10:ℝ) = ((9*k : ℕ):ℝ) := by push_cast; ring
  rw [h, Real.rpow_natCast]

private theorem delta_upper (s k : ℕ) (h : s ≤ 2^(10*k)) :
    rootDelta s ≤ 2^(9*k) := by
  unfold rootDelta
  apply Nat.ceil_le.mpr
  have hh : (s:ℝ) ≤ ((2^(10*k):ℕ):ℝ) := by exact_mod_cast h
  exact (Real.rpow_le_rpow (by positivity) hh (by norm_num : (0:ℝ) ≤ 9/10)).trans_eq (dyadic_rpow k)

private theorem delta_lower (s k : ℕ) (h : 2^(10*k) ≤ s) :
    2^(9*k) ≤ rootDelta s := by
  have hh : (((2^(10*k):ℕ):ℝ)) ≤ (s:ℝ) := by exact_mod_cast h
  have lePower := Real.rpow_le_rpow (by positivity) hh (by norm_num : (0:ℝ) ≤ 9/10)
  rw [dyadic_rpow] at lePower
  have leCeil : (s:ℝ)^(9/10:ℝ) ≤ (rootDelta s : ℝ) :=
    (Nat.ceil_le (n:=rootDelta s)).mp (le_refl _)
  exact_mod_cast lePower.trans leCeil

theorem u_large (s : ℕ) (h : 2^(9*131072-1) < s) : 9 ≤ rootU s := by
  have H := (Nat.lt_clog_iff_pow_lt (by decide : 1 < (2:ℕ))).2 h
  unfold rootU
  omega

theorem root_exponent (s : ℕ) (h : 0 < rootU s) : rootT s+1 = 2*rootU s := by
  unfold rootT
  omega

/-- Discharge the three original packing inequalities at the root by
comparing exact dyadic integers, including the ceil in Delta. No real
limit theorem is assumed. -/
theorem root_packing (s M : ℕ) (hS : 2 ≤ s) (hM : s ≤ M) (hu : 9 ≤ rootU s) :
    let t := rootT s
    131072 ≤ printedL t ∧
    2*(printedD t)^2*rootDelta s ≤ M ∧
    printedL t*printedD t ≤ M ∧ 2*printedL t ≤ rootDelta s := by
  let lam := Nat.clog 2 s
  let a := 2*rootU s
  let k := lam/10
  have hsHi : s ≤ (2:ℕ)^lam := Nat.le_pow_clog (by decide) _
  have hsLo : (2:ℕ)^(lam-1) < s := Nat.pow_pred_clog_lt_self (by decide) (by omega)
  have ht : rootT s+1 = a := root_exponent s (by omega)
  have hL : printedL (rootT s) = 2^a := by rw [printedL,ht]
  have hD : printedD (rootT s) = 2^(12*a) := by
    rw [printedD_is_L12,hL,← pow_mul]
    congr 1
    omega
  have hloExp : 10*(k-1) ≤ lam-1 := by
    have hk : 10*k ≤ lam := by dsimp [k]; omega
    omega
  have hhiExp : lam ≤ 10*(k+1) := by dsimp [k]; omega
  have hf1 : 1+24*a+9*(k+1) ≤ lam-1 := by
    dsimp [a, rootU, k, lam]
    unfold rootU at hu
    omega
  have hf2 : 13*a ≤ lam-1 := by
    dsimp [a, rootU, lam]
    unfold rootU at hu
    omega
  have hf3 : 1+a ≤ 9*(k-1) := by
    dsimp [a, rootU, k, lam]
    unfold rootU at hu
    omega
  have hf4 : 17 ≤ a := by dsimp [a]; omega
  have hdu := delta_upper s (k+1) (hsHi.trans (Nat.pow_le_pow_right (by decide) hhiExp))
  have hdl := delta_lower s (k-1) ((Nat.pow_le_pow_right (by decide) hloExp).trans hsLo.le)
  have hm : (2:ℕ)^(lam-1) ≤ M := hsLo.le.trans hM
  dsimp only
  rw [hD,hL]
  refine ⟨?_,?_,?_,?_⟩
  · exact (show 131072 = (2:ℕ)^17 by decide).le.trans (Nat.pow_le_pow_right (by decide) hf4)
  · calc
      _ ≤ 2*((2:ℕ)^(12*a))^2*2^(9*(k+1)) := Nat.mul_le_mul_left _ hdu
      _ = 2^(1+24*a+9*(k+1)) := by
        change (2:ℕ)^1*((2:ℕ)^(12*a))^2*2^(9*(k+1)) = _
        rw [← pow_mul, ← pow_add, ← pow_add]
        congr 1
        omega
      _ ≤ M := (Nat.pow_le_pow_right (by decide) hf1).trans hm
  · calc
      _ = (2:ℕ)^(13*a) := by rw [← pow_add]; congr 1; omega
      _ ≤ M := (Nat.pow_le_pow_right (by decide) hf2).trans hm
  · calc
      _ = (2:ℕ)^(1+a) := by rw [pow_add,pow_one]
      _ ≤ 2^(9*(k-1)) := Nat.pow_le_pow_right (by decide) hf3
      _ ≤ _ := hdl

theorem four_clone_root_packing (N : ℕ) (he : N%2=0)
    (large : 2^(9*131072-1) < sourceSize N) :
    let t := rootT (sourceSize N)
    let Δ := rootDelta (sourceSize N)
    131072 ≤ printedL t ∧ 2*(printedD t)^2*Δ ≤ 24*N ∧
      printedL t*printedD t ≤ 24*N ∧ 2*printedL t ≤ Δ := by
  apply root_packing
  · have hu := u_large _ large
    unfold rootU at hu
    have hlog : 1 < Nat.clog 2 (sourceSize N) := by omega
    have hb : (2:ℕ)^1 < sourceSize N := (Nat.lt_clog_iff_pow_lt (by decide : 1 < (2:ℕ))).1 hlog
    exact hb.le
  · exact (source_size N he).2
  · exact u_large _ large

#print axioms source_size
#print axioms root_packing
#print axioms four_clone_root_packing

end
end J7PrintedParams
