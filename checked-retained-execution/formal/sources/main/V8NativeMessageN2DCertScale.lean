import P5HybridClosurePrintedGrowth
import J1PPrintedSize

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 15500000
set_option exponentiation.threshold 1024

/-! Literal Appendix D parameters used in the printed all-leaves error.
These describe only a numerical envelope, not the balance of any
packing whose actual labels have no collision certificate. -/
namespace V8NativeMessage.N2DCert
open Real Filter Paper5.HybridClosure.Printed J1PPrinted J9PrintedSchedule
open scoped Topology

noncomputable section

abbrev nativeH (s : ℕ) : ℕ := leafThreshold s (Nat.clog 2 s)

def eta (s : ℕ) : ℝ :=
  (s:ℝ)^(1/1000:ℝ)*sqrt (2*(sourceDelta s:ℝ)/(nativeH s:ℝ))

def callError (s M D : ℕ) : ℝ :=
  (D:ℝ)*sqrt (2*(sourceDelta s:ℝ)/(M:ℝ))

theorem eta_nonnegative (s : ℕ) : 0≤eta s := by
  unfold eta
  positivity

theorem threshold_real_cover (s : ℕ) (hs : 2≤s) :
    0 < nativeH s ∧ (s:ℝ)≤(nativeH s:ℝ)*sqrt (Nat.clog 2 s:ℝ) := by
  let lam := Nat.clog 2 s
  have hl : 0 < lam := by
    change 0 < Nat.clog 2 s
    apply (Nat.lt_clog_iff_pow_lt (by decide)).mpr
    simp
    omega
  have hCover : s≤nativeH s*lam.sqrt := le_roundup_mul s lam.sqrt (Nat.sqrt_pos.2 hl)
  have hPos : 0 < nativeH s := by
    by_contra! hn
    have he : nativeH s=0 := by omega
    rw [he,zero_mul] at hCover
    omega
  have hCast : (s:ℝ)≤(nativeH s:ℝ)*(lam.sqrt:ℝ) := by exact_mod_cast hCover
  exact ⟨hPos,hCast.trans (mul_le_mul_of_nonneg_left
    (sqrt_nat_le_real lam) (by positivity))⟩

theorem threshold_inverse_upper (s : ℕ) (hs : 2≤s) :
    1/(nativeH s:ℝ)≤sqrt (Nat.clog 2 s:ℝ)/(s:ℝ) := by
  have h := threshold_real_cover s hs
  have hc : (0:ℝ)<nativeH s := by exact_mod_cast h.1
  have hs' : (0:ℝ)<s := by exact_mod_cast (show 0<s by omega)
  apply (div_le_div_iff₀ hc hs').2
  simpa only [one_mul,mul_one,mul_comm] using h.2

theorem delta_double_upper (s : ℕ) (hs : 1≤s) :
    (sourceDelta s:ℝ)≤2*(s:ℝ)^(9/10:ℝ) := by
  have hR : (1:ℝ)≤s := by exact_mod_cast hs
  have hu : 1≤(s:ℝ)^(9/10:ℝ) := one_le_rpow hR (by norm_num)
  have h := Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity : (0:ℝ)≤s) (9/10:ℝ))
  change (sourceDelta s:ℝ)<(s:ℝ)^(9/10:ℝ)+1 at h
  linarith only [hu,h]

theorem printed_array_rpow_bound (s depth : ℕ)
    (hu : 1≤rootU (Nat.clog 2 s)) :
    (stepD (Nat.clog 2 s) depth:ℝ)≤(s:ℝ)^(1/1000:ℝ) := by
  let D := stepD (Nat.clog 2 s) depth
  have hD : (D:ℝ)^1000≤(s:ℝ) := by
    exact_mod_cast (dimensions_small s depth hu).2.le
  have h := rpow_le_rpow (by positivity : 0≤(D:ℝ)^1000) hD
    (by norm_num : 0≤(1/1000:ℝ))
  rw [←rpow_natCast_mul (by positivity : (0:ℝ)≤D) 1000,
    show ((1000:ℕ):ℝ)*(1/1000:ℝ)=1 by norm_num,rpow_one] at h
  exact h

theorem uniform_call_error (s M depth : ℕ) (hs : 2≤s)
    (hu : 1≤rootU (Nat.clog 2 s)) (hM : nativeH s<M) :
    callError s M (stepD (Nat.clog 2 s) depth)≤eta s := by
  have hH : (0:ℝ)<nativeH s := by exact_mod_cast (threshold_real_cover s hs).1
  have hc : ((nativeH s:ℕ):ℝ)≤M := by exact_mod_cast hM.le
  unfold callError eta
  exact mul_le_mul (printed_array_rpow_bound s depth hu)
    (sqrt_le_sqrt (div_le_div_of_nonneg_left (by positivity) hH hc))
    (sqrt_nonneg _) (rpow_nonneg (by positivity) _)

/-- The additive margin computed from the actual cell counts is the
same multiplicative error, not a square-root factor approximation. -/
theorem scale_call_error (s M D : ℕ) (hM : 0<M) :
    (D:ℝ)*sqrt (2*(M:ℝ)*(sourceDelta s:ℝ))=(M:ℝ)*callError s M D := by
  have hM' : (0:ℝ)<M := by exact_mod_cast hM
  have hRoot : sqrt (2*(M:ℝ)*(sourceDelta s:ℝ)) =
      (M:ℝ)*sqrt (2*(sourceDelta s:ℝ)/(M:ℝ)) := by
    calc
      _ = sqrt ((M:ℝ)^2*(2*(sourceDelta s:ℝ)/(M:ℝ))) := by
        congr 1
        field_simp [hM'.ne']
      _ = _ := by rw [sqrt_mul (by positivity),sqrt_sq hM'.le]
  rw [hRoot]
  unfold callError
  ring

#print axioms eta_nonnegative
#print axioms threshold_real_cover
#print axioms threshold_inverse_upper
#print axioms delta_double_upper
#print axioms printed_array_rpow_bound
#print axioms uniform_call_error
#print axioms scale_call_error
end
end V8NativeMessage.N2DCert
