import V8NativeMessageN8LiteralChart
import V8NativeMessageN8LiteralPrintedMath

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2550000

/-! The original sufficiently-large-size N8 conclusion using the
literal four-copy size and actual printed root schedule. -/
namespace V8NativeMessage.N8Literal
open scoped Classical Polynomial
open Polynomial J6R12Blueprint J6R10Repack P11FullPacking J1PPrinted
open Paper5.HybridClosure Paper5.HybridClosure.Printed Paper5.D1Literal
open V8NativeMessage.N4 V8NativeMessage.N6D

noncomputable section

theorem source_cutoff_exists (γ : ℝ) (hγ : 0<γ) :
    ∃ n₀ : ℕ, ∀ N i q : ℕ, n₀≤N → q≤dA N+1-i →
      68*(sourcePayload N i q:ℝ)<γ*(N:ℝ) := by
  obtain ⟨K,hK⟩ := exists_nat_gt (68/γ)
  have h68 : (68:ℝ)≤γ*(K:ℝ) := by
    apply le_of_lt
    simpa only [mul_comm] using (div_lt_iff₀ hγ).mp hK
  refine ⟨(2:ℕ)^(2*(11*K+4)+2),?_⟩
  intro N i q hN hq
  have hsmall : (K:ℝ)*(sourcePayload N i q:ℝ)<(N:ℝ) := by
    exact_mod_cast source_payload_small N i q K hq hN
  calc
    _ ≤ (γ*(K:ℝ))*(sourcePayload N i q:ℝ) :=
      mul_le_mul_of_nonneg_right h68 (by positivity)
    _ = γ*((K:ℝ)*(sourcePayload N i q:ℝ)) := by ring
    _ < _ := mul_lt_mul_of_pos_left hsmall hγ

section Concrete
variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))

include reg in
theorem actual_old_row_size : oldRowSize F=dSize (Fintype.card W) := by
  have h := oldRow_size_exact F reg
  unfold dSize
  omega

include reg in
theorem actual_printed_a : (S).levelBits 0=dA (Fintype.card W) := by
  change stepA (Nat.clog 2 (oldRowSize F)) 0=dA (Fintype.card W)
  rw [actual_old_row_size F reg]
  simp [stepA,stepU,epsDen,dA,dLambda,J9PrintedSchedule.rootA,J9PrintedSchedule.rootU]

include reg in
theorem exact_printed_tape (i : rootKept F f) (q : ℕ) :
    messageBits F i q=sourcePayload (Fintype.card W) i.val.val q := by
  unfold messageBits sourcePayload
  exact congrArg (fun a : ℕ => (2^a/2^i.val.val)*(q*(q+1)/2)) (actual_printed_a (f:=f) F reg)

end Concrete


#print axioms source_cutoff_exists
#print axioms actual_old_row_size
#print axioms actual_printed_a
#print axioms exact_printed_tape

end
end V8NativeMessage.N8Literal
