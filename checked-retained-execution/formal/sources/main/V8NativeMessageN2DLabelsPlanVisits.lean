import V8NativeMessageN2DLabelsSelector
import J6R12BlueprintReach

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
set_option maxRecDepth 2200
set_option linter.unusedSectionVars false

/-! Preserve the label certificate on every occurrence in the actual
padded source Blueprint. A visit is a path of its real addresses; a
bare proposition of reachability would erase repeated occurrences. -/
namespace V8NativeMessage.N2DLabels
open scoped Classical Polynomial
open Polynomial J6ActiveRun J6R9Recursive J6R10Reachable J6R10Repack
open J6R11Blueprint J6R12Blueprint J1PPrinted

section Visit
variable {Host Mode : Type*} [Fintype Mode] [DecidableEq Mode]
  {S : Shape Host Mode} {Value : ℕ→Type*}

inductive ActualVisit (P : Program S Value) (root : Call Host) : Call Host→Type _ where
  | base : ActualVisit P root root
  | down {c : Call Host} (prior : ActualVisit P root c) (active : S.cutoff<c.edges)
      (addr : Address S c) : ActualVisit P root (P.child c addr)

theorem ActualVisit.reached {P : Program S Value} {root c : Call Host}
    (v : ActualVisit P root c) : Reach P root c := by
  induction v with
  | base => exact .base
  | down _ active addr ih => exact .down ih active addr

theorem actual_visit_iff {P : Program S Value} {root c : Call Host} :
    Nonempty (ActualVisit P root c)↔Reach P root c := by
  constructor
  · rintro ⟨p⟩
    exact p.reached
  · intro h
    induction h with
    | base => exact ⟨.base⟩
    | down _ live address ih =>
      obtain ⟨p⟩ := ih
      exact ⟨.down p live address⟩
end Visit

section Source
variable {f : ℤ[X]} {ell s C : ℕ}
local notation "SP" => printedParams (f:=f) (ell:=ell) s
local notation "D" => sourceDelta s

theorem source_reached_native (sel : CertifiedSelector SP D)
    (root : Call (PhysicalHost f ell)) (hf : f.Monic)
    [DecidableEq (Envelope (N (forget sel)) (Childs (forget sel)) root)]
    {c : Call (PhysicalHost f ell)} (seen : Reach (sourceBlueprint (forget sel) root hf).program root c) :
    NativeReach (Plan (forget sel)) root c := by
  exact (paddedBlueprint_exact_reachable (N (forget sel)) (Childs (forget sel)) root
    (positive_at_native (forget sel) root) f ell (physicalEntries hf) c).1 seen

theorem active_source_reachable_ready (sel : CertifiedSelector SP D)
    (root : Call (PhysicalHost f ell)) (hf : f.Monic)
    [DecidableEq (Envelope (N (forget sel)) (Childs (forget sel)) root)]
    (cfg : RootBounds s C f) (stable : Stable s C root) {c : Call (PhysicalHost f ell)}
    (seen : Reach (sourceBlueprint (forget sel) root hf).program root c)
    (live : (SP).cutoff<c.edges) : Ready SP D c := by
  exact ready_reachable cfg (forget sel) (source_reached_native sel root hf seen) stable live

theorem active_source_reachable_collision (sel : CertifiedSelector SP D)
    (root : Call (PhysicalHost f ell)) (hf : f.Monic)
    [DecidableEq (Envelope (N (forget sel)) (Childs (forget sel)) root)]
    (cfg : RootBounds s C f) (stable : Stable s C root) {c : Call (PhysicalHost f ell)}
    (seen : Reach (sourceBlueprint (forget sel) root hf).program root c) (live : (SP).cutoff<c.edges) :
    CollisionCertified D (packing (forget sel)
      (active_source_reachable_ready sel root hf cfg stable seen live)) := by
  exact selected_variance sel (active_source_reachable_ready sel root hf cfg stable seen live)

theorem active_source_visit_collision (sel : CertifiedSelector SP D)
    (root : Call (PhysicalHost f ell)) (hf : f.Monic)
    [DecidableEq (Envelope (N (forget sel)) (Childs (forget sel)) root)]
    (cfg : RootBounds s C f) (stable : Stable s C root) {c : Call (PhysicalHost f ell)}
    (visit : ActualVisit (sourceBlueprint (forget sel) root hf).program root c) (live : (SP).cutoff<c.edges) :
    CollisionCertified D (packing (forget sel)
      (active_source_reachable_ready sel root hf cfg stable visit.reached live)) := by
  exact active_source_reachable_collision sel root hf cfg stable visit.reached live

theorem repeated_occurrence_same_labels (sel : CertifiedSelector SP D)
    (root : Call (PhysicalHost f ell)) (hf : f.Monic)
    [DecidableEq (Envelope (N (forget sel)) (Childs (forget sel)) root)]
    (cfg : RootBounds s C f) (stable : Stable s C root) {c : Call (PhysicalHost f ell)}
    (first second : ActualVisit (sourceBlueprint (forget sel) root hf).program root c)
    (live : (SP).cutoff<c.edges) :
    packing (forget sel) (active_source_reachable_ready sel root hf cfg stable first.reached live) =
      packing (forget sel) (active_source_reachable_ready sel root hf cfg stable second.reached live) :=
  rfl
end Source


#print axioms ActualVisit.reached
#print axioms actual_visit_iff
#print axioms source_reached_native
#print axioms active_source_reachable_ready
#print axioms active_source_reachable_collision
#print axioms active_source_visit_collision

#print axioms repeated_occurrence_same_labels
end V8NativeMessage.N2DLabels
