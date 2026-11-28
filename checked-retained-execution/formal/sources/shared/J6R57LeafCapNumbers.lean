import J6R16ModeCostCompress

/-! The numerical D.4.7 leaf comparison: the input entry exponent in
D.1 is at most the actual printed leaf threshold, including its ceiling. -/
namespace J6R57LeafCap
open J1PPrinted J6R16ModeCost
set_option autoImplicit false
set_option warningAsError true

theorem printed_log_pow5_le_size (s : ℕ) (large : 1024≤Nat.clog 2 s) :
    (Nat.clog 2 s)^5≤s := by
  let lam := Nat.clog 2 s
  let u := lam-2
  change 1024≤lam at large
  have hu : 32≤u := by unfold u; omega
  have hlam : lam≤2*u := by unfold u; omega
  have hbelow : (2:ℕ)^(lam-1)<s :=
    (Nat.lt_clog_iff_pow_lt (by decide : 1<(2:ℕ))).mp (by change lam-1<lam; omega)
  calc
    _≤(2*u)^5 := Nat.pow_le_pow_left hlam _
    _=2*(16*u^5) := by ring
    _≤2*(2:ℕ)^u := Nat.mul_le_mul_left 2 (sixteen_pow5_le u hu)
    _=(2:ℕ)^(lam-1) := by rw [show lam-1=u+1 by unfold u; omega,pow_succ]; ring
    _≤s := hbelow.le

theorem source_delta_le_actual_leaf_threshold (s : ℕ) (large : 1024≤Nat.clog 2 s) :
    sourceDelta s≤J9PrintedSchedule.leafThreshold s (Nat.clog 2 s) := by
  let lam := Nat.clog 2 s
  let H := J9PrintedSchedule.leafThreshold s lam
  change 1024≤lam at large
  have hs : 0<s := by
    have h : (2:ℕ)^(lam-1)<s :=
      (Nat.lt_clog_iff_pow_lt (by decide : 1<(2:ℕ))).mp (by change lam-1<lam; omega)
    exact (Nat.zero_le _).trans_lt h
  have hsr : 0<(s:ℝ) := by exact_mod_cast hs
  have hPos : 0<lam.sqrt := Nat.sqrt_pos.mpr (by omega)
  have hPosR : 0<(lam.sqrt:ℝ) := by exact_mod_cast hPos
  have hTen : lam.sqrt^10≤s := by
    calc
      _=(lam.sqrt*lam.sqrt)^5 := by ring
      _≤lam^5 := Nat.pow_le_pow_left (Nat.sqrt_le lam) _
      _≤s := printed_log_pow5_le_size s large
  have grow : (lam.sqrt:ℝ)≤(s:ℝ)^(1/10:ℝ) := by
    calc
      _=(((lam.sqrt:ℝ)^10):ℝ)^(1/10:ℝ) := by
        rw [← Real.rpow_natCast_mul hPosR.le 10]
        norm_num
      _≤_ := Real.rpow_le_rpow (by positivity) (by exact_mod_cast hTen) (by norm_num)
  have head : s≤H*lam.sqrt := J9PrintedSchedule.le_roundup_mul s lam.sqrt hPos
  have headR : (s:ℝ)≤(H:ℝ)*(lam.sqrt:ℝ) := by exact_mod_cast head
  have e : (s:ℝ)^(9/10:ℝ)*(lam.sqrt:ℝ)≤(H:ℝ)*(lam.sqrt:ℝ) := by
    calc
      _≤(s:ℝ)^(9/10:ℝ)*(s:ℝ)^(1/10:ℝ) :=
        mul_le_mul_of_nonneg_left grow (Real.rpow_nonneg hsr.le _)
      _=(s:ℝ) := by rw [← Real.rpow_add hsr]; norm_num
      _≤_ := headR
  unfold sourceDelta
  exact Nat.ceil_le.mpr (le_of_mul_le_mul_right e hPosR)

#print axioms printed_log_pow5_le_size
#print axioms source_delta_le_actual_leaf_threshold
end J6R57LeafCap
