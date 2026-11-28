import P5HybridClosurePrintedD

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

/-! The original N8 printed message size is o(N), with a conservative
integer-only threshold. Constants are from the true four-copy Appendix
D schedule, not the five-copy pooled-menu terminal bound. -/
namespace V8NativeMessage.N8Literal
open Paper5.HybridClosure.Printed

private theorem succ_le_pow2 (n : ℕ) : n+1≤(2:ℕ)^n := by
  induction n with
  | zero => decide
  | succ n ih => rw [pow_succ]; omega

def sourcePayload (N i q : ℕ) : ℕ := (2^dA N/2^i)*(q*(q+1)/2)

theorem source_payload_small (N i q K : ℕ)
    (cap : q≤dA N+1-i)
    (large : (2:ℕ)^(2*(11*K+4)+2)≤N) :
    K*sourcePayload N i q<N := by
  let lam := dLambda N
  let a := dA N
  let u := dU N
  let k := 11*K+4
  have hlam : 2*k+2≤lam := by
    have h : (2:ℕ)^(2*k+2)≤(2:ℕ)^lam :=
      large.trans ((d_size_bounds N).1.trans (Nat.le_pow_clog (by decide) (dSize N)))
    exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp h
  have hAu : a=2*u := rfl
  have hscale : 131072*u≤lam := (J9PrintedSchedule.rootU_range lam).1
  have ha : 3*a+2≤lam/2 := by
    have h8 : 8≤lam := by dsimp [k] at hlam; omega
    omega
  have hq : q≤a+1 := cap.trans (Nat.sub_le _ _)
  have ht : q*(q+1)/2≤((2:ℕ)^(a+1))*((2:ℕ)^(a+1)) := by
    apply (Nat.div_le_self _ _).trans
    exact Nat.mul_le_mul (hq.trans (by have h := succ_le_pow2 (a+1); omega))
      ((Nat.succ_le_succ hq).trans (succ_le_pow2 (a+1)))
  have hb : sourcePayload N i q≤(2:ℕ)^(lam/2) := by
    calc
      _ ≤ (2:ℕ)^a*((2:ℕ)^(a+1)*(2:ℕ)^(a+1)) :=
        Nat.mul_le_mul (Nat.div_le_self _ _) ht
      _ = (2:ℕ)^(3*a+2) := by rw [← pow_add,← pow_add]; congr 1; omega
      _ ≤ _ := Nat.pow_le_pow_right (by decide) ha
  have hK : 11*K≤(2:ℕ)^k := by
    exact (show 11*K≤k+1 by dsimp [k]; omega).trans (succ_le_pow2 k)
  have hk : k+lam/2≤lam-1 := by omega
  have hmul : 11*(K*sourcePayload N i q)≤(2:ℕ)^(lam-1) := by
    rw [← Nat.mul_assoc]
    calc
      _ ≤ (2:ℕ)^k*(2:ℕ)^(lam/2) := Nat.mul_le_mul hK hb
      _ ≤ _ := by rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) hk
  have hs : (2:ℕ)^(lam-1)<dSize N := by
    apply (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).mp
    change lam-1<lam
    omega
  have h := (hmul.trans_lt hs).trans_le (d_size_bounds N).2
  omega

#print axioms source_payload_small
end V8NativeMessage.N8Literal
