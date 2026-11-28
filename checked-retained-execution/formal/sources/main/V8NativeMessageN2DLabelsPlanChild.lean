import V8NativeMessageN2DLabelsPlanVisits
import V8NativeMessageN2DLabelsPlanNative

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2200
set_option maxHeartbeats 1500000

/-! Exact child-address correspondence on a visit of the unchanged
certified source plan. No projected packet is rebuilt. -/
namespace V8NativeMessage.N2DLabels
open scoped Classical Polynomial
open Polynomial J6ActiveRun J6R9Recursive J6R10Reachable J6R10Repack
open J6R11Blueprint J6R12Blueprint J1PPrinted

variable {f : ℤ[X]} {ell s C : ℕ}
local notation "SP" => printedParams (f:=f) (ell:=ell) s
local notation "D" => sourceDelta s

/-- Decode the very address used at this source visit, with its real
selected packing; no related or same-size child is substituted. -/
noncomputable def native_at_source (sel : CertifiedSelector SP D)
    (root : Call (PhysicalHost f ell)) (hf : f.Monic)
    [DecidableEq (Envelope (N (forget sel)) (Childs (forget sel)) root)]
    {c : Call (PhysicalHost f ell)}
    (visit : ActualVisit (sourceBlueprint (forget sel) root hf).program root c)
    (live : (SP).cutoff<c.edges)
    (w : Address (paddedShape (N (forget sel)) (Childs (forget sel)) root) c) :
    (Plan (forget sel)).Slot c :=
  let h := source_reached_native sel root hf visit.reached
  ⟨(nativeAddressEquiv (N (forget sel)) (Childs (forget sel)) root c h live
    (positive_at_native (forget sel) root c h live)).symm w,live⟩

theorem native_source_address_roundtrip (sel : CertifiedSelector SP D)
    (root : Call (PhysicalHost f ell)) (hf : f.Monic)
    [DecidableEq (Envelope (N (forget sel)) (Childs (forget sel)) root)]
    {c : Call (PhysicalHost f ell)}
    (visit : ActualVisit (sourceBlueprint (forget sel) root hf).program root c)
    (live : (SP).cutoff<c.edges)
    (w : Address (paddedShape (N (forget sel)) (Childs (forget sel)) root) c) :
    let h := source_reached_native sel root hf visit.reached
    nativeAddressEquiv (N (forget sel)) (Childs (forget sel)) root c h live
      (positive_at_native (forget sel) root c h live) (native_at_source sel root hf visit live w).val=w :=
  Equiv.apply_symm_apply _ _

theorem actual_source_address_indices (sel : CertifiedSelector SP D)
    (root : Call (PhysicalHost f ell)) (hf : f.Monic)
    [DecidableEq (Envelope (N (forget sel)) (Childs (forget sel)) root)]
    {c : Call (PhysicalHost f ell)}
    (visit : ActualVisit (sourceBlueprint (forget sel) root hf).program root c)
    (live : (SP).cutoff<c.edges)
    (w : Address (paddedShape (N (forget sel)) (Childs (forget sel)) root) c) :
    let a := (native_at_source sel root hf visit live w).val
    w.t=a.1 ∧ w.zeta=a.2.1 ∧ w.group=a.2.2.2 := by
  let h := source_reached_native sel root hf visit.reached
  let v := (native_at_source sel root hf visit live w).val
  have hh := address_indices (N (forget sel)) (Childs (forget sel)) root c h live
    (positive_at_native (forget sel) root c h live) v
  change
    (nativeAddressEquiv (N (forget sel)) (Childs (forget sel)) root c h live
      (positive_at_native (forget sel) root c h live) v).t=v.1 ∧
    (nativeAddressEquiv (N (forget sel)) (Childs (forget sel)) root c h live
      (positive_at_native (forget sel) root c h live) v).zeta=v.2.1 ∧
    (nativeAddressEquiv (N (forget sel)) (Childs (forget sel)) root c h live
      (positive_at_native (forget sel) root c h live) v).group=v.2.2.2 at hh
  rw [native_source_address_roundtrip sel root hf visit live w] at hh
  exact hh

theorem actual_source_native_child (sel : CertifiedSelector SP D)
    (root : Call (PhysicalHost f ell)) (hf : f.Monic)
    [DecidableEq (Envelope (N (forget sel)) (Childs (forget sel)) root)]
    {c : Call (PhysicalHost f ell)}
    (visit : ActualVisit (sourceBlueprint (forget sel) root hf).program root c)
    (live : (SP).cutoff<c.edges)
    (w : Address (paddedShape (N (forget sel)) (Childs (forget sel)) root) c) :
    (sourceBlueprint (forget sel) root hf).program.child c w =
      (Plan (forget sel)).child c (native_at_source sel root hf visit live w) :=
  paddedBlueprint_child (N (forget sel)) (Childs (forget sel)) root
    (positive_at_native (forget sel) root) f ell (physicalEntries hf) c
    (source_reached_native sel root hf visit.reached) live w

theorem actual_source_slot_child (sel : CertifiedSelector SP D)
    (root : Call (PhysicalHost f ell)) (hf : f.Monic)
    [DecidableEq (Envelope (N (forget sel)) (Childs (forget sel)) root)]
    (cfg : RootBounds s C f) (seed : Stable s C root) {c : Call (PhysicalHost f ell)}
    (visit : ActualVisit (sourceBlueprint (forget sel) root hf).program root c)
    (live : (SP).cutoff<c.edges)
    (w : Address (paddedShape (N (forget sel)) (Childs (forget sel)) root) c) :
    let d := active_source_reachable_ready sel root hf cfg seed visit.reached live
    let addr := native_at_source sel root hf visit live w
    let packet := packetOfSite (forget sel) d addr.val.1 addr.val.2.1
      (siteTuple (forget sel) d addr.val) addr.val.2.2.2
    (sourceBlueprint (forget sel) root hf).program.child c w =
      ⟨packet,c.depth+1,packet.edgeCount,registerPrecision SP c addr.val.1⟩ ∧
      CollisionCertified D (packing (forget sel) d) := by
  let d := active_source_reachable_ready sel root hf cfg seed visit.reached live
  let addr := native_at_source sel root hf visit live w
  exact ⟨(actual_source_native_child sel root hf visit live w).trans
    (child_exact (forget sel) d addr.val),selected_variance sel d⟩

#print axioms native_at_source
#print axioms native_source_address_roundtrip
#print axioms actual_source_address_indices
#print axioms actual_source_native_child
#print axioms actual_source_slot_child
end V8NativeMessage.N2DLabels