import V8NativeMessageN7LiteralSupportCertificateCompose

/-! Uniform finite volume of component-local verification. A promise
on the actual local bit counts is explicit; this is not an algorithm
for finding a layout or a metering of the native contraction. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical BigOperators
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000
noncomputable section

variable {S C K : Type} [Fintype S] [Fintype C] [Fintype K]

theorem component_local_table_check_volume
    (pinOwner : S→K) (colOwner : C→K)
    (n m d : ℕ) (withinLog : 2^m≤n)
    (size : ∀ k,Fintype.card (Fiber pinOwner k) + Fintype.card (Fiber colOwner k)≤m*d) :
    (∑ k, Fintype.card ((Fiber pinOwner k→Bool)×(Fiber colOwner k→Bool))) ≤
      Fintype.card K * n^d := by
  calc
    _ ≤ ∑ _k : K,n^d := by
      refine Finset.sum_le_sum fun k _=>?_
      rw [actual_certificate_word_pair_count]
      calc
        _ ≤ (2:ℕ)^(m*d) := Nat.pow_le_pow_right (by decide) (size k)
        _ = ((2:ℕ)^m)^d := pow_mul _ _ _
        _ ≤ _ := Nat.pow_le_pow_left withinLog _
    _ = _ := by simp

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.component_local_table_check_volume
