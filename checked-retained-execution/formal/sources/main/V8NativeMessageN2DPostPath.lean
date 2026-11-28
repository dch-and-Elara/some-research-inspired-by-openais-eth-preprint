import V8NativeMessageC3NativeAssemblyN2Printed
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 16500000

/-! The frozen largest-child descent and the frozen physical leaf fold
are joined at the exact same requested (t, probe, mode). Only the group
changes during the first step. No claim about an arbitrary child. -/
namespace V8NativeMessage.N2DPost
open Real Polynomial J6ActiveRun J6R9Recursive J6R10Reachable
  J6R12Blueprint J6R11Blueprint J1PPrinted
  V8NativeMessage.C3.NativeAssembly
open scoped Polynomial Classical BigOperators

noncomputable section

def paidLeafAssignments (m : ℕ) : ℕ :=
  J6ChildPlan.allBits m (fun _ => (1:ℕ))

theorem leaf_log_exact (m : ℕ) :
    logb 2 (paidLeafAssignments m:ℝ)=(m:ℝ) := by
  have h2 : logb 2 2=1 := by simp
  rw [paidLeafAssignments,J6ChildPlan.allBits_visits,Nat.cast_pow,Nat.cast_ofNat,logb_pow,h2,mul_one]

theorem leaf_log_strict (H m : ℕ) (hs : H<32*m) :
    (H:ℝ)/32<logb 2 (paidLeafAssignments m:ℝ) := by
  rw [leaf_log_exact]
  apply (div_lt_iff₀ (by norm_num : (0:ℝ)<32)).mpr
  rw [mul_comm]
  exact_mod_cast hs

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))

include cfg in
theorem requested_largest_actual_leaf
    (root : Call (PhysicalHost f ell)) (seed : Stable s C root) (hf : f.Monic)
    (w : (FactoryPlan sel).Slot root) :
    let B := sourceBlueprint sel root hf
    let H := (printedParams (f:=f) (ell:=ell) s).cutoff
    ∃ g : Fin 64,
      (∀ j, ((FactoryPlan sel).child root (regroupNative sel root w j)).edges≤
        ((FactoryPlan sel).child root (regroupNative sel root w g)).edges) ∧
      ∃ d : Call (PhysicalHost f ell),
        NativeReach (FactoryPlan sel) ((FactoryPlan sel).child root (regroupNative sel root w g)) d ∧
        Reach B.program root d ∧
        B.program.run d = J6ChildPlan.allBits d.edges
          (fun x=>reduce d.prec f ell (physicalEntries hf d x).prod) ∧
        2^(H/32)<paidLeafAssignments d.edges ∧
        2^H<(paidLeafAssignments d.edges)^32 ∧
        (H:ℝ)/32<logb 2 (paidLeafAssignments d.edges:ℝ) := by
  obtain ⟨g,hMax,d,hTail,hLeaf,hSize⟩ := leaf_from_requested_slot cfg sel root seed w
  have fromRoot : NativeReach (FactoryPlan sel) root d :=
    NativeReach.step (regroupNative sel root w g) hTail
  have done := physical_terminal_at_native_path (J6R12Blueprint.N sel) (Childs sel) root
    (positive_at_native sel root) hf d fromRoot hLeaf hSize
  exact ⟨g,hMax,d,hTail,done.1,done.2.1,done.2.2.1,done.2.2.2,leaf_log_strict _ _ hSize⟩

#print axioms leaf_log_exact
#print axioms leaf_log_strict
#print axioms requested_largest_actual_leaf
end
end V8NativeMessage.N2DPost
