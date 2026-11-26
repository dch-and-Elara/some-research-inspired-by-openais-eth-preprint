import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-! Elementary pointwise fair-binomial lower probability as needed in
F.A2. The central mass bound comes from the exact adjacent recurrences;
the off-centre bound sums their logarithms. No Stirling estimate is assumed. -/
namespace P5MainIterator
open scoped BigOperators Classical
open Real

noncomputable def fairPoint (n j : ℕ) : ℝ := (n.choose j:ℝ)/(2:ℝ)^n

theorem fairPoint_nonneg (n j : ℕ) : 0≤fairPoint n j := by unfold fairPoint; positivity

theorem fairPoint_pos (n j : ℕ) (h : j≤n) : 0<fairPoint n j := by
  unfold fairPoint
  have h' : 0<(n.choose j:ℝ) := by exact_mod_cast Nat.choose_pos h
  positivity

noncomputable def midpointFactor (m : ℕ) : ℝ :=
  (2*(m:ℝ)+1)/(2*(m:ℝ)+2)

theorem midpoint_odd_step (m : ℕ) :
    fairPoint (2*m+1) m = midpointFactor m * fairPoint (2*m) m := by
  have h := Nat.choose_mul_succ_eq (2*m) m
  rw [show 2*m+1-m=m+1 by omega] at h
  have hB : ((2*m).choose m : ℝ) * (2*(m:ℝ)+1) =
      (((2*m+1).choose m : ℕ):ℝ) * ((m:ℝ)+1) := by exact_mod_cast h
  unfold fairPoint midpointFactor
  rw [pow_succ]
  field_simp
  linarith only [hB]

theorem midpoint_even_step (m : ℕ) :
    fairPoint (2*(m+1)) (m+1) = midpointFactor m * fairPoint (2*m) m := by
  have h := Nat.succ_mul_choose_eq (2*m+1) m
  have hA : (2*m+1+1) * (2*m+1).choose m = (2*m+1+1).choose (m+1) * (m+1) := h
  have hc : (2*(m+1)).choose (m+1) = 2*((2*m+1).choose m) := by
    apply Nat.eq_of_mul_eq_mul_right (by omega : 0<m+1)
    rw [show 2*(m+1)=2*m+1+1 by omega,←hA]
    ring
  rw [←midpoint_odd_step, fairPoint, fairPoint,hc,show 2*(m+1)=2*m+1+1 by omega,pow_succ]
  push_cast
  ring

theorem sqrt_near_middle (m : ℕ) :
    sqrt (m:ℝ) ≤ midpointFactor m * sqrt ((m:ℝ)+1) := by
  have hf : 0≤midpointFactor m := by unfold midpointFactor; positivity
  calc
    _ ≤ sqrt ((midpointFactor m * sqrt ((m:ℝ)+1))^2) := by
      apply sqrt_le_sqrt
      rw [mul_pow,Real.sq_sqrt (by positivity)]
      unfold midpointFactor
      rw [div_pow,div_mul_eq_mul_div]
      apply (le_div_iff₀ (by positivity)).mpr
      have h : 0≤(m:ℝ)+1 := by positivity
      nlinarith only [h]
    _ = _ := by rw [sqrt_sq (mul_nonneg hf (sqrt_nonneg _))]

theorem central_even_lower (m : ℕ) (hm : 1≤m) :
    1≤2*sqrt (m:ℝ)*fairPoint (2*m) m := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hm
  induction k with
  | zero => norm_num [fairPoint,Nat.choose]
  | succ k ih =>
    have hf := fairPoint_nonneg (2*(1+k)) (1+k)
    calc
      _ ≤ 2*sqrt ((1+k:ℕ):ℝ) * fairPoint (2*(1+k)) (1+k) := ih (by omega)
      _ ≤ 2*(midpointFactor (1+k) * sqrt (((1+k:ℕ):ℝ)+1)) *
            fairPoint (2*(1+k)) (1+k) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sqrt_near_middle _) (by norm_num)) hf
      _ = _ := by
        rw [show 1+(k+1)=(1+k)+1 by omega,midpoint_even_step]
        push_cast
        ring

theorem fair_middle_mass (n : ℕ) (hn : 2≤n) :
    1/(4*sqrt (n:ℝ)) ≤ fairPoint n (n/2) := by
  let m := n/2
  have hm : 1≤m := by dsimp [m]; omega
  have hcentral := central_even_lower m hm
  have hsqrt : sqrt (m:ℝ) ≤ sqrt (n:ℝ) := sqrt_le_sqrt (by exact_mod_cast (by dsimp [m]; omega : m≤n))
  have hpos : 0<sqrt (n:ℝ) := sqrt_pos.2 (by exact_mod_cast (by omega : 0<n))
  have hfactor : (1/2:ℝ)≤midpointFactor m := by
    unfold midpointFactor
    apply (le_div_iff₀ (by positivity)).mpr
    linarith only [(show 0≤(m:ℝ) by positivity)]
  apply (div_le_iff₀ (by positivity : 0<4*sqrt (n:ℝ))).mpr
  have H : fairPoint (2*m) m / 2≤fairPoint n m := by
    have hne : n=2*m ∨ n=2*m+1 := by dsimp [m]; omega
    rcases hne with h | h
    · conv_rhs => rw [h]
      have hh := fairPoint_nonneg (2*m) m
      linarith only [hh]
    · conv_rhs => rw [h,midpoint_odd_step]
      rw [div_eq_mul_inv,mul_comm]
      exact mul_le_mul_of_nonneg_right (by simpa only [one_div] using hfactor) (fairPoint_nonneg _ _)
  calc
    _ ≤ 2*sqrt (m:ℝ)*fairPoint (2*m) m := hcentral
    _ = (fairPoint (2*m) m/2)*(4*sqrt (m:ℝ)) := by ring
    _ ≤ fairPoint n m * (4*sqrt (n:ℝ)) :=
      mul_le_mul H (mul_le_mul_of_nonneg_left hsqrt (by norm_num)) (by positivity) (fairPoint_nonneg _ _)

theorem fairPoint_adjacent (n i : ℕ) (hi : i<n) :
    fairPoint n (i+1) = fairPoint n i * (((n:ℝ)-(i:ℝ))/((i:ℝ)+1)) := by
  have he := Nat.succ_mul_choose_eq (n-1) i
  have hf := Nat.choose_mul_succ_eq (n-1) i
  have hN : n-1+1=n := by omega
  change (n-1+1)*(n-1).choose i=(n-1+1).choose (i+1)*(i+1) at he
  rw [hN] at he hf
  have hg : n.choose (i+1)*(i+1) = n.choose i*(n-i) := he.symm.trans (by simpa only [Nat.mul_comm] using hf)
  have hr : (n.choose (i+1):ℝ)*((i:ℝ)+1) = (n.choose i:ℝ)*((n:ℝ)-(i:ℝ)) := by
    have h : (↑(n.choose (i+1)):ℝ)*(↑(i+1):ℝ) = (↑(n.choose i):ℝ)*(↑(n-i):ℝ) := by exact_mod_cast hg
    push_cast [Nat.cast_sub hi.le] at h
    exact h
  unfold fairPoint
  field_simp
  linarith only [hr]

theorem lower_log_step (n i : ℕ) (hi : n / 2 ≤ i) (hq : 8 * i ≤ 7 * n) (hn : 0 < n) :
    log (fairPoint n i) - (8/(n:ℝ))*(2*(i:ℝ)+1-(n:ℝ)) ≤ log (fairPoint n (i+1)) := by
  have hil : i<n := by omega
  have hn' : 0<(n:ℝ) := by exact_mod_cast hn
  have hnr : 0<(n:ℝ)-(i:ℝ) := sub_pos.mpr (by exact_mod_cast hil)
  have hfi := fairPoint_pos n i hil.le
  have he : (n:ℝ)≤2*(i:ℝ)+1 := by exact_mod_cast (by omega : n≤2*i+1)
  have hq' : 8*(i:ℝ)≤7*(n:ℝ) := by exact_mod_cast hq
  have hnum : 0≤2*(i:ℝ)+1-(n:ℝ) := sub_nonneg.mpr he
  have hden : (n:ℝ)/8 ≤ (n:ℝ)-(i:ℝ) := by linarith only [hq']
  have h₁ := log_le_sub_one_of_pos (div_pos (show 0<(i:ℝ)+1 by positivity) hnr)
  have h₂ : ((i:ℝ)+1) / ((n:ℝ)-(i:ℝ))-1 =
      (2*(i:ℝ)+1-(n:ℝ))/((n:ℝ)-(i:ℝ)) := by field_simp; ring
  rw [h₂,log_div (by positivity) hnr.ne'] at h₁
  have h₃ := div_le_div_of_nonneg_left hnum (show 0<(n:ℝ)/8 by positivity) hden
  have h₄ : (2*(i:ℝ)+1-(n:ℝ))/((n:ℝ)/8) = (8/(n:ℝ))*(2*(i:ℝ)+1-(n:ℝ)) := by ring
  rw [h₄] at h₃
  rw [fairPoint_adjacent n i hil,log_mul hfi.ne' (by positivity),log_div hnr.ne' (by positivity)]
  linarith only [h₁,h₃]

theorem log_window_telescope (n d : ℕ) (hn : 0<n) (hd : 8*(n/2+d)≤7*n) :
    log (fairPoint n (n/2)) - (8/(n:ℝ))*(d:ℝ)^2 ≤ log (fairPoint n (n/2+d)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hs := lower_log_step n (n/2+d) (by omega) (by omega) hn
    have hp := ih (by omega)
    have hmid : 2*((n/2:ℕ):ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 2*(n/2)≤n)
    push_cast at hs
    have hcoef : 0≤(8/(n:ℝ)) := by positivity
    have h := mul_le_mul_of_nonneg_left
      (show 2*(((n/2:ℕ):ℝ)+d)+1-(n:ℝ) ≤ 2*(d:ℝ)+1 by linarith only [hmid]) hcoef
    push_cast
    rw [show n/2+(d+1)=n/2+d+1 by omega]
    nlinarith only [hs,hp,h]

theorem fair_binomial_point_lower (n d : ℕ) (hn : 2≤n) (hd : 8*(n/2+d)≤7*n) :
    (1/(4*sqrt (n:ℝ))) * exp (-(8/(n:ℝ))*(d:ℝ)^2) ≤ fairPoint n (n/2+d) := by
  have hp : 0<fairPoint n (n/2+d) := fairPoint_pos n _ (by omega)
  have hu : 0<1/(4*sqrt (n:ℝ)) := by positivity
  have hl := log_le_log hu (fair_middle_mass n hn)
  have h := log_window_telescope n d (by omega) hd
  apply (log_le_log_iff (mul_pos hu (exp_pos _)) hp).mp
  rw [log_mul hu.ne' (exp_ne_zero _),log_exp]
  linarith only [h,hl]

#print axioms midpoint_odd_step
#print axioms midpoint_even_step
#print axioms central_even_lower
#print axioms fair_middle_mass
#print axioms lower_log_step
#print axioms log_window_telescope
#print axioms fair_binomial_point_lower
end P5MainIterator
