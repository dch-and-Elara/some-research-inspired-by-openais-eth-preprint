import V8NativeMessageN2DLabelsSelector
import J6R12BlueprintReach

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1500
set_option maxHeartbeats 700000

/-! The native dependency is direct: the same projected selector
is used for readiness, the actual child factory and the certificate. -/
namespace V8NativeMessage.N2DLabels
open scoped Polynomial Classical
open J6ActiveRun J6R10Reachable J6R10Repack J6R11Blueprint J6R12Blueprint
open J6R9Recursive J1PPrinted

variable {f : ℤ[X]} {ell s C : ℕ}
local notation "SP" => printedParams (f:=f) (ell:=ell) s
local notation "D" => sourceDelta s

theorem native_source_ready (sel : CertifiedSelector SP D)
    (cfg : RootBounds s C f) {root c : Call (PhysicalHost f ell)} (seed : Stable s C root)
    (seen : NativeReach (Plan (forget sel)) root c)
    (live : (SP).cutoff<c.edges) : Ready SP D c := by
  exact ready_reachable cfg (forget sel) seen seed live

theorem native_source_collision (sel : CertifiedSelector SP D)
    (cfg : RootBounds s C f) {root c : Call (PhysicalHost f ell)} (seed : Stable s C root)
    (seen : NativeReach (Plan (forget sel)) root c) (live : (SP).cutoff<c.edges) :
    CollisionCertified D (packing (forget sel) (native_source_ready sel cfg seed seen live)) := by
  exact selected_variance sel (native_source_ready sel cfg seed seen live)

theorem native_source_slot_certificate (sel : CertifiedSelector SP D)
    (cfg : RootBounds s C f) {root c : Call (PhysicalHost f ell)} (seed : Stable s C root)
    (seen : NativeReach (Plan (forget sel)) root c)
    (w : (Plan (forget sel)).Slot c) :
    let d := native_source_ready sel cfg seed seen w.property
    let child := packetOfSite (forget sel) d w.val.1 w.val.2.1
      (siteTuple (forget sel) d w.val) w.val.2.2.2
    (Plan (forget sel)).child c w=
      ⟨child,c.depth+1,child.edgeCount,registerPrecision SP c w.val.1⟩ ∧
      CollisionCertified D (packing (forget sel) d) := by
  let d := native_source_ready sel cfg seed seen w.property
  exact ⟨child_exact (forget sel) d w.val,selected_variance sel d⟩


#print axioms native_source_ready
#print axioms native_source_collision
#print axioms native_source_slot_certificate
end V8NativeMessage.N2DLabels
