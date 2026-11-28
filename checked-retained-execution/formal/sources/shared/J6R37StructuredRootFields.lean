import J6R37StructuredRootEmitBase

namespace J6R37StructuredRoot
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R31RootResidentTables J6R32RootGeneratedRegistryInputs
open J6R34RootAtlas J6R36ChildFramedRoute J6R35GatewayPreparation J6R35RootOrigins
open J6R27OriginalGate J6R30GeneratedRootLayout J6R26StablePreparedRoot
open J6Mesh J6OrientedHost J6R24LegalLayout J6R11Repack J6R10Repack
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6000000
set_option maxRecDepth 3000

set_option maxHeartbeats 8000000

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)

theorem source_lane_row_paid (gate : Stamp key prec) (pad : ℕ) (h : Port (RootWire m)) :
    birthLanes m pad gate ⟨X.issue.result,X.birth⟩ ((rootParent X).record h)=
      ⟨actualLane X gate pad h,laneFee m pad key prec⟩ := by
  change birthLanes m pad gate ⟨X.issue.result,X.birth⟩
    (halfPortSpec m (side h) (physicalSeatField (rootChart T) (oddAxis m)
      (residentPageKey m) (edge h)))=_
  rw [birth_lanes_exact]
  unfold actualLane
  rw [actual_outer_stamp]

private theorem map_meter_member {A B : Type*} (q : A→Meter B) {l : List A} {a : A}
    (h : a∈l) : (q a).result∈(J6R12CollisionEdges.mapMeter q l).result := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    change (q a).result∈((q x).result::(J6R12CollisionEdges.mapMeter q xs).result)
    rcases List.mem_cons.mp h with equal|rest
    · subst a
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih rest)

theorem selected_root_lane (gate : Stamp key prec) (pad : ℕ) (h : Port (RootWire m))
    (groupEq : physicalGroup (G.selector ell) (G.ready ell) (G.centre ell X.centre) h=X.group) :
    actualLane X gate pad h∈(outerLanes X gate pad).result.lanes := by
  let F := outerLanes X gate pad
  let D := rootParent X
  let q := birthLanes m pad gate ⟨X.issue.result,X.birth⟩
  have hit : h∈D.physicalSelected X.group :=
    List.mem_filter.mpr ⟨D.complete h,decide_eq_true groupEq⟩
  have selected : (D.record h)∈F.result.selected := by
    rw [outer_selected_input X gate pad]
    exact List.mem_map.mpr ⟨h,hit,rfl⟩
  have found : (q (D.record h)).result∈F.result.lanes := map_meter_member q selected
  have row : (q (D.record h)).result=actualLane X gate pad h :=
    congrArg Meter.result (source_lane_row_paid X gate pad h)
  rw [row] at found
  exact found

#print axioms source_lane_row_paid
#print axioms selected_root_lane
end J6R37StructuredRoot