import V8NativeMessageC3NativeAssemblyN2Local
import J6ChildPlan

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

namespace V8NativeMessage.C3.NativeAssembly
open J6R10Reachable

/-- Structural reachability, independent of the coefficient ring.
A step must be an actual member of the plan's finite address set. -/
theorem reach_large_literal_leaf {A : Type*} (P : FinitePlan A) (H : ℕ)
    (Q : A→Prop)
    (step : ∀ c, Q c → H<P.size c → ∃ w : P.Slot c,
       Q (P.child c w) ∧ P.size c≤32*P.size (P.child c w))
    (c : A) (hQ : Q c) (hsize : H<32*P.size c) :
    ∃ d, NativeReach P c d ∧ Q d ∧ P.size d≤H ∧ H<32*P.size d := by
  by_cases hh : P.size c≤H
  · exact ⟨c,.reflexive c,hQ,hh,hsize⟩
  · have ha := Nat.lt_of_not_ge hh
    obtain ⟨w,hC,hw⟩ := step c hQ ha
    obtain ⟨d,hR,hQ',hH,hD⟩ := reach_large_literal_leaf P H Q step (P.child c w) hC (ha.trans_le hw)
    exact ⟨d,.step w hR,hQ',hH,hD⟩
termination_by P.size c
decreasing_by exact P.smaller c w

theorem actual_assignment_leaf_numeric (H n : ℕ) (h : H<32*n) :
    2^H<(J6ChildPlan.allBits n (fun _ => (1:ℕ)))^32 := by
  rw [J6ChildPlan.allBits_visits,←pow_mul]
  exact Nat.pow_lt_pow_right (by decide) (by omega)

#print axioms reach_large_literal_leaf
#print axioms actual_assignment_leaf_numeric
end V8NativeMessage.C3.NativeAssembly
