import V8R45PooledLiteralSchedule
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3600000
set_option maxRecDepth 2700

/-! Exact finite estimates underlying the displayed C4 scale. In
particular the receiving budget is bounded uniformly over every legal
choice of precisions, not after holding one list constant. -/
namespace V8R45PooledLiteral
open scoped Polynomial
open V8PooledMenu V8PooledMenu.FiveCopy

private def denom : ℕ := 128*1024

private theorem root_bits_floor (V : Type) [Fintype V] :
    denom*rootA V ≤ 2*Nat.clog 2 (rootSize V) := by
  have h : denom*rootU V ≤ Nat.clog 2 (rootSize V) := by
    unfold denom rootU
    simp only [Nat.mul_comm (128*1024)]
    exact Nat.div_mul_le_self _ _
  unfold rootA
  rw [Nat.mul_left_comm]
  exact Nat.mul_le_mul_left _ h

private theorem pow_clog_lt_twice (s : ℕ) (hs : 2≤s) :
    (2:ℕ)^Nat.clog 2 s < 2*s := by
  let L := Nat.clog 2 s
  have hL : 0<L := Nat.clog_pos (by decide) hs
  have hPow : (2:ℕ)^(L-1)<s :=
    (Nat.lt_clog_iff_pow_lt (by decide)).mp (by omega : L-1<Nat.clog 2 s)
  calc
    (2:ℕ)^L = 2*(2:ℕ)^(L-1) := by
      conv_lhs => rw [show L=(L-1)+1 by omega, pow_succ']
    _ < 2*s := by omega

theorem C4_explicit_printed_power_log (V : Type) [Fintype V] (P : PublicPrecision V) :
    (pooledBits (rootA V) (rootU V) P.prec : ℝ) <
    2 * (2 * (rootSize V : ℝ))^((2:ℝ)/(128*1024)) *
      ((Nat.clog 2 (rootSize V) : ℝ)+2)^2 := by
  let s := rootSize V
  let lam := Nat.clog 2 s
  let a := rootA V
  let e := (2:ℝ)/(128*1024)
  have hs : 2≤s := by unfold s rootSize; omega
  have he : 0≤e := by unfold e; positivity
  have hdNat : (128*1024:ℕ)*a ≤ 2*lam := root_bits_floor V
  have hd : (128*1024:ℝ)*(a:ℝ) ≤ 2*(lam:ℝ) := by exact_mod_cast hdNat
  have hcast : (a:ℝ) ≤ (lam:ℝ)*e := by
    unfold e
    rw [←mul_div_assoc,le_div_iff₀ (by norm_num : (0:ℝ)<128*1024),mul_comm (lam:ℝ) 2]
    linarith
  have hpow : (2:ℝ)^a ≤ (2*(s:ℝ))^e := by
    rw [←Real.rpow_natCast]
    calc
      (2:ℝ)^(a:ℝ) ≤ (2:ℝ)^((lam:ℝ)*e) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hcast
      _ = ((2:ℝ)^lam)^e := by rw [Real.rpow_mul (by norm_num : (0:ℝ)≤2),Real.rpow_natCast]
      _ ≤ (2*(s:ℝ))^e := Real.rpow_le_rpow (by positivity)
        (by exact_mod_cast (pow_clog_lt_twice s hs).le) he
  have ha : a≤lam := by omega
  have hh : (triangle (a+1):ℝ) ≤ ((lam:ℝ)+2)^2 := by
    have h : triangle (a+1) ≤ (lam+2)^2 := by
      unfold triangle
      rw [pow_two]
      exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul (by omega) (by omega))
    exact_mod_cast h
  have h₀ : (pooledBits (rootA V) (rootU V) P.prec : ℝ) <
      2*(2:ℝ)^a*(triangle (a+1):ℝ) := by
    exact_mod_cast source_C4_strict P
  exact h₀.trans_le (mul_le_mul (mul_le_mul_of_nonneg_left hpow (by norm_num))
    hh (by positivity) (by positivity))

private theorem succ_le_pow_two (a : ℕ) : a+1≤(2:ℕ)^a := by
  induction a with
  | zero => decide
  | succ n ih =>
    rw [pow_succ]
    omega

theorem C4_square_strictly_sublinear (V : Type) [Fintype V] (P : PublicPrecision V) :
    (pooledBits (rootA V) (rootU V) P.prec)^2 < rootSize V := by
  let a := rootA V
  let u := rootU V
  let s := rootSize V
  let lam := Nat.clog 2 s
  let B := pooledBits a u P.prec
  have hs : 2≤s := by unfold s rootSize; omega
  by_cases hu : u=0
  · have hB : B=0 := by
      haveI : IsEmpty (Fin u) := ⟨fun i => by have h := i.isLt; omega⟩
      simp only [B,pooledBits,Finset.univ_eq_empty,Finset.sum_empty]
    change B^2 < s
    rw [hB]
    omega
  · have ha : a=2*u := rfl
    have hroot : denom*a≤2*lam := root_bits_floor V
    have hCalc : 2*(3*a+3)≤lam-1 := by
      unfold denom at hroot
      omega
    have htri : triangle (a+1) ≤ (2:ℕ)^(a+1)*(2:ℕ)^(a+1) := by
      unfold triangle
      exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul
        ((Nat.le_succ (a+1)).trans (succ_le_pow_two (a+1))) (succ_le_pow_two (a+1)))
    have hB : B < (2:ℕ)^(3*a+3) := by
      calc
        B < (2*2^a)*triangle (a+1) := source_C4_strict P
        _ ≤ (2*2^a)*((2:ℕ)^(a+1)*(2:ℕ)^(a+1)) := Nat.mul_le_mul_left _ htri
        _ = (2:ℕ)^(3*a+3) := by rw [←pow_succ',←pow_add,←pow_add]; congr 1; omega
    have hlam : 0<lam := Nat.clog_pos (by decide) hs
    have hEnd : (2:ℕ)^(lam-1)<s :=
      (Nat.lt_clog_iff_pow_lt (by decide)).mp (by omega : lam-1<Nat.clog 2 s)
    have hx : (2:ℕ)^(3*a+3) * (2:ℕ)^(3*a+3) ≤ (2:ℕ)^(lam-1) := by
      rw [←pow_add]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    change B^2 < s
    rw [pow_two]
    exact ((Nat.mul_le_mul hB.le hB.le).trans hx).trans_lt hEnd

#print axioms C4_explicit_printed_power_log
#print axioms C4_square_strictly_sublinear
end V8R45PooledLiteral