import J6R57ActiveFeeGeometry

/-! The exponential-looking dyadic grid scale is linear in printed s;
the inherited and individual receiving width envelope is polynomial
in s and the actual starting precision. -/
namespace J6R57ActiveFee
open J6R50Peak
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000
set_option Elab.async false

theorem printed_log_le_size (s : ℕ) : Nat.clog 2 s ≤ s :=
  (Nat.clog_le_iff_le_pow (by decide : 1<(2:ℕ))).2 (show s < (2:ℕ)^s from Nat.lt_two_pow_self).le

theorem actual_dyadic_size_linear (s : ℕ) (hs : 1<s) : (2:ℕ)^Nat.clog 2 s ≤ 2*s := by
  have positive : 0<Nat.clog 2 s := by
    apply (Nat.lt_clog_iff_pow_lt (by decide : 1<(2:ℕ))).2
    simpa only [pow_zero] using hs
  have h := Nat.pow_pred_clog_lt_self (by decide : 1<(2:ℕ)) hs
  have eq : Nat.clog 2 s=(Nat.clog 2 s-1)+1 := by omega
  calc
    _=2^((Nat.clog 2 s-1)+1) := congrArg (fun n : ℕ=>(2:ℕ)^n) eq
    _≤2*s := by
      rw [pow_succ,Nat.mul_comm 2 s]
      exact Nat.mul_le_mul_right 2 h.le

def printedPrecisionPoly (s C p : ℕ) := p+(32*(C*s))*(64*s+8*(s+1))

theorem absolute_precision_is_polynomial {s C M p : ℕ} (hs : 1<s) (hM : M≤C*s) :
    absolutePrecision s M p ≤ printedPrecisionPoly s C p := by
  have m : 32*M/29 ≤ 32*(C*s) :=
    (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ hM)
  have d := actual_dyadic_size_linear s hs
  have l := printed_log_le_size s
  have h : edgePrecisionSlope s ≤ 64*s+8*(s+1) := by
    unfold edgePrecisionSlope
    have scale : 32*(2:ℕ)^Nat.clog 2 s ≤ 64*s :=
      (Nat.mul_le_mul_left 32 d).trans_eq (by ring)
    exact Nat.add_le_add scale (Nat.mul_le_mul_left _ (Nat.succ_le_succ l))
  exact Nat.add_le_add_left (Nat.mul_le_mul m h) p

theorem real_probe_envelope_is_quadratic {s C : ℕ} (hs : 1<s) :
    (C*s)*(2*2^(Nat.clog 2 s))+1 ≤ (C*s)*(4*s)+1 := by
  have m := Nat.mul_le_mul_left 2 (actual_dyadic_size_linear s hs)
  have n : 2*(2*s)=4*s := by ring
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (m.trans_eq n)) 1

#print axioms printed_log_le_size
#print axioms actual_dyadic_size_linear
#print axioms absolute_precision_is_polynomial
#print axioms real_probe_envelope_is_quadratic
end J6R57ActiveFee
