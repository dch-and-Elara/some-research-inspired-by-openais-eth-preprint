import V8NativeMessageN2DPostNumeric
import V8NativeMessageN2DPostPath

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 22000000

/-! Literal Appendix D v8 N2: for every required root address on the
printed four-clone size, the maximum-child path reaches an actual
printed exhaustive leaf whose paid visit exponent is Omega(N/sqrt(log N)).
Nothing here substitutes an arbitrary child for that maximum. -/
namespace V8NativeMessage.N2DPost
open Real Polynomial Paper5.HybridClosure.Printed J6ActiveRun J6R9Recursive
  J6R10Reachable J6R12Blueprint J6R11Blueprint J1PPrinted
  V8NativeMessage.C3.NativeAssembly
open scoped Polynomial Classical BigOperators

noncomputable section

variable {f : ℤ[X]} {ell C : ℕ}

theorem printed_D_requested_largest_omega (N : ℕ) (hN : 2≤N)
    (cfg : RootBounds (dSize N) C f)
    (sel : Selector (printedParams (f:=f) (ell:=ell) (dSize N)) (sourceDelta (dSize N)))
    (root : Call (PhysicalHost f ell)) (seed : Stable (dSize N) C root) (hf : f.Monic)
    (w : (FactoryPlan sel).Slot root) :
    let B := sourceBlueprint sel root hf
    ∃ g : Fin 64,
      (∀ j, ((FactoryPlan sel).child root (regroupNative sel root w j)).edges≤
        ((FactoryPlan sel).child root (regroupNative sel root w g)).edges) ∧
      ∃ d : Call (PhysicalHost f ell),
        NativeReach (FactoryPlan sel) ((FactoryPlan sel).child root (regroupNative sel root w g)) d ∧
        Reach B.program root d ∧
        B.program.run d = J6ChildPlan.allBits d.edges
          (fun x=>reduce d.prec f ell (physicalEntries hf d x).prod) ∧
        (threshold N:ℝ)/32<logb 2 (paidLeafAssignments d.edges:ℝ) ∧
        dCoeff*rate N<logb 2 (paidLeafAssignments d.edges:ℝ) := by
  obtain ⟨g,hMax,d,hTail,hReach,hExact,_,_,hLog⟩ :=
    requested_largest_actual_leaf cfg sel root seed hf w
  have hH : (threshold N:ℝ)/32<logb 2 (paidLeafAssignments d.edges:ℝ) := hLog
  exact ⟨g,hMax,d,hTail,hReach,hExact,hH,(d_threshold_log_bound N hN).trans_lt hH⟩

#print axioms printed_D_requested_largest_omega
end
end V8NativeMessage.N2DPost
