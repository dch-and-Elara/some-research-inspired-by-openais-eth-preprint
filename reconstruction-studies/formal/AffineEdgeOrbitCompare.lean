import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open Filter
open scoped Topology

namespace AffineEdge.Orbit

noncomputable section

private theorem pow_four_residue (q : ℕ) : ∃ k : ℕ, 4^q = 3*k+1 := by
  induction q with
  | zero => exact ⟨0,rfl⟩
  | succ q ih =>
    obtain ⟨k,hk⟩ := ih
    refine ⟨4*k+1,?_⟩
    rw [pow_succ,hk]
    omega

private theorem zero_arithmetic (q : ℕ) (hq : 1 ≤ q) :
    2*((2^(2*q)-2^q)/2 : ℕ) + 2^q = (2^q)*(2^q) ∧
    3*((4^q-1)/3 : ℕ) + 1 = (2^q)*(2^q) := by
  have hn : 2 ∣ (2:ℕ)^q := by
    obtain ⟨j,rfl⟩ : ∃ j, q = j+1 := ⟨q-1,by omega⟩
    exact ⟨2^j, by rw [pow_succ, Nat.mul_comm]⟩
  obtain ⟨k,hk⟩ := pow_four_residue q
  have hs : (2:ℕ)^q ≤ 2^q * 2^q := by
    have hp : 0 < (2:ℕ)^q := Nat.pow_pos (by decide)
    exact Nat.le_mul_of_pos_right _ hp
  have hd : 2 ∣ ((2:ℕ)^q * 2^q - 2^q) := Nat.dvd_sub (dvd_mul_of_dvd_left hn _) hn
  have he : (2:ℕ)^(2*q) = 2^q * 2^q := by rw [two_mul,pow_add]
  constructor
  · rw [he, Nat.mul_div_cancel' hd, Nat.sub_add_cancel hs]
  · have hf : (4:ℕ)^q = 2^q * 2^q := by rw [← mul_pow]; rfl
    rw [← hf,hk]
    omega

theorem zero_rank_strict (q : ℕ) (hq : 2 ≤ q) :
    (4^q-1)/3 < ((2^(2*q)-2^q)/2 : ℕ) := by
  obtain ⟨h₀,h₁⟩ := zero_arithmetic q (by omega)
  have hn : 4 ≤ (2:ℕ)^q := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hq
  have hh : 4 * (2:ℕ)^q ≤ 2^q * 2^q := Nat.mul_le_mul_right _ hn
  omega

theorem boundary_rank_strict (q : ℕ) (hq : 2 ≤ q) :
    q + (q+1)/2 + 2 < 2*q+2 := by omega

theorem zero_rank_ratio (q : ℕ) (hq : 1 ≤ q) :
    (((2^(2*q)-2^q)/2 : ℕ) : ℝ) / (((4^q-1)/3 : ℕ) : ℝ) =
      3*(2:ℝ)^q/(2*((2:ℝ)^q+1)) := by
  let x : ℝ := (((2^(2*q)-2^q)/2 : ℕ) : ℝ)
  let y : ℝ := (((4^q-1)/3 : ℕ) : ℝ)
  let n : ℝ := (2:ℝ)^q
  have hx : 2*x+n = n*n := by
    dsimp [x,n]
    exact_mod_cast (zero_arithmetic q hq).1
  have hy : 3*y+1 = n*n := by
    dsimp [y,n]
    exact_mod_cast (zero_arithmetic q hq).2
  have hn : 2 ≤ n := by
    have h : 2 ≤ (2:ℕ)^q := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hq
    dsimp [n]
    exact_mod_cast h
  have hxy : x = n*(n-1)/2 ∧ y = (n-1)*(n+1)/3 := by
    constructor <;> nlinarith [hx,hy]
  change x / y = 3*n/(2*(n+1))
  rw [hxy.1,hxy.2]
  have h₀ : n-1 ≠ 0 := by linarith
  have h₁ : n+1 ≠ 0 := by linarith
  field_simp

theorem zero_ratio_limit :
    Tendsto (fun q : ℕ => 3*(2:ℝ)^q/(2*((2:ℝ)^q+1))) atTop (𝓝 (3/2 : ℝ)) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat.comp
    (Nat.tendsto_pow_atTop_atTop_of_one_lt (m := 2) (by decide))
  have h' : Tendsto (fun q : ℕ => (3/2 : ℝ) - (3/2) * (1 / ((2:ℝ)^q+1)))
      atTop (𝓝 (3/2 : ℝ)) := by
    simpa [Function.comp_def] using
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul h) :
        Tendsto _ atTop (𝓝 ((3/2 : ℝ) - (3/2)*0)))
  apply h'.congr
  intro q
  have hn : 0 < (2:ℝ)^q + 1 := by positivity
  field_simp
  ring

def boundaryRatio (q : ℕ) : ℝ :=
  ((2*q+2 : ℕ) : ℝ) / ((q+(q+1)/2+2 : ℕ) : ℝ)

theorem boundary_ratio_limit : Tendsto boundaryRatio atTop (𝓝 (4/3 : ℝ)) := by
  let e (q : ℕ) : ℝ := ((q % 2 : ℕ) : ℝ) / q
  have he : Tendsto e atTop (𝓝 0) := by
    apply squeeze_zero _ _ tendsto_one_div_atTop_nhds_zero_nat
    · intro q
      exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · intro q
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast (show q % 2 ≤ 1 by omega)
  have h₁ := tendsto_const_div_atTop_nhds_zero_nat 2
  have hh : Tendsto (fun q : ℕ => ((2:ℝ)+2/q)/((3/2:ℝ)+e q/2+2/q))
      atTop (𝓝 ((2:ℝ)/(3/2))) := by
    have hj := he.div_const (2:ℝ)
    simpa using (tendsto_const_nhds.add h₁).div
      ((tendsto_const_nhds.add hj).add h₁) (by norm_num : (3/2:ℝ)+0/2+0 ≠ 0)
  have hLim : (2:ℝ)/(3/2) = 4/3 := by norm_num
  rw [hLim] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with q hq
  have hq' : (q:ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hpar : (2:ℝ)*(((q+1)/2 : ℕ):ℝ) = (q:ℝ) + ((q%2 : ℕ):ℝ) := by
    exact_mod_cast (show 2*((q+1)/2) = q+q%2 by omega)
  unfold boundaryRatio e
  push_cast
  rw [show (((q+1)/2 : ℕ):ℝ) = ((q:ℝ)+((q%2 : ℕ):ℝ))/2 by linarith]
  have hnn : (0:ℝ) ≤ ((q%2 : ℕ):ℝ) := Nat.cast_nonneg _
  have hpos : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  field_simp
  ring

end
end AffineEdge.Orbit
