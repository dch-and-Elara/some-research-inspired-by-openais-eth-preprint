import J6R79NumericEnvelope

/-! Compare the fixed printed exponent and depth prefactor with the
original D.1 scale, including its ceiling and floor. These facts do not
turn generated owner or word producers into entry oracles. -/
namespace J6R79Numeric
open J6R16ModeCost J6R57LeafCap J1PPrinted

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 6000000

theorem printed_clog_le_size (s : ℕ) : Nat.clog 2 s≤s :=
  (Nat.clog_le_iff_le_pow (by decide : 1<(2:ℕ))).2
    ((Nat.le_succ _).trans (J9PrintedSchedule.next_le_two_power s))

theorem printed_depth_prefactor (s C d : ℕ) (hC : 0<C) (hLam : 0<Nat.clog 2 s)
    (hSize : (2*epsDen)^30*C^10≤Nat.clog 2 s) :
    pathLimit s C-d+1≤s+2 := by
  have path := (path_limit_le s C hC hLam hSize).trans
    (Nat.add_le_add_right (printed_clog_le_size s) 1)
  have floor := Nat.sub_le (pathLimit s C) d
  omega

theorem original_vertex_allowance_fits_printed_leaf (s L b A : ℕ)
    (large : 1024≤Nat.clog 2 s) :
    (s+L)^b*2^(A*sourceDelta s)≤
      (s+L)^b*2^(A*J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)) :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide)
    (Nat.mul_le_mul_left _ (source_delta_le_actual_leaf_threshold s large)))

theorem printed_leaf_exponent_le_s_over_sqrt_log (s : ℕ) (hs : 1<s) :
    (J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) : ℝ)≤
      4*(s:ℝ)/Real.sqrt (Nat.clog 2 s : ℝ) := by
  let n := Nat.clog 2 s
  let d := n.sqrt
  let H := J9PrintedSchedule.leafThreshold s n
  have hn : 0<n := (Nat.lt_clog_iff_pow_lt (by decide : 1<(2:ℕ))).2
    (by simpa using hs)
  have hd : 0<d := Nat.sqrt_pos.2 hn
  have ds : d≤s := (Nat.sqrt_le_self n).trans (printed_clog_le_size s)
  have hFloor : H*d≤s+d-1 := Nat.div_mul_le_self _ _
  have h2 : H*d≤2*s := by omega
  have hStep : n<(d+1)^2 := Nat.sqrt_lt'.1 (Nat.lt_succ_self d)
  have hStepR : (n:ℝ)≤((d:ℝ)+1)^2 := by exact_mod_cast hStep.le
  have hSqrt : Real.sqrt (n:ℝ)≤2*(d:ℝ) := by
    have hUpper := Real.sqrt_le_sqrt hStepR
    rw [Real.sqrt_sq (by positivity : 0≤(d:ℝ)+1)] at hUpper
    have hOne : (1:ℝ)≤d := by exact_mod_cast hd
    linarith only [hUpper,hOne]
  have hPos : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  change (H:ℝ)≤4*(s:ℝ)/Real.sqrt (n:ℝ)
  apply (le_div_iff₀ hPos).2
  have h2R : (H:ℝ)*(d:ℝ)≤2*(s:ℝ) := by exact_mod_cast h2
  calc
    _≤(H:ℝ)*(2*(d:ℝ)) := mul_le_mul_of_nonneg_left hSqrt (by positivity)
    _=2*((H:ℝ)*(d:ℝ)) := by ring
    _≤4*(s:ℝ) := by linarith only [h2R]

#print axioms printed_depth_prefactor
#print axioms original_vertex_allowance_fits_printed_leaf
#print axioms printed_leaf_exponent_le_s_over_sqrt_log
end J6R79Numeric
