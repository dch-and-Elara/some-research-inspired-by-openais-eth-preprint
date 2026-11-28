import J6R37StructuredRootCore
import J6R35GatewayPreparationRender
import J6R35RootOriginsStable

/-! Use the same fixed exterior occurrence, the same immutable shared
parent array and the same counted group selection. The untouched R26
header and the new separately metered lane array share that selection. -/
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

structure ExteriorLanes (m key prec pad : ℕ) where
  header : DirRow key
  selected : List (PortRow (rootHalfWidth m))
  lanes : List (RootLanes m key prec pad)

def emitLanes {m key prec b d : ℕ} (J : J6R26DescriptorTree.Job (rootHalfWidth m) b d prec)
    (issue : Meter (Word key)) (gate : Stamp key prec) (pad : ℕ) :
    Meter (ExteriorLanes m key prec pad) :=
  let count := childPortsWithCount (b:=b) J.group J.ports
  let depth := increment J.parentDepth
  let bytes := serializeRows count.result.1
  let fixed := writeChildHeader issue.result J.precision depth.result count.result.2 bytes.result
  let all := copyBytes (J.coordinates++fixed.result.bytes)
  let priced := issue.steps+count.steps+depth.steps+bytes.steps+fixed.steps+6+
      all.steps+3*J.coordinates.length+5
  let lanes := J6R12CollisionEdges.mapMeter (birthLanes m pad gate ⟨issue.result,J.precision⟩) count.result.1
  ⟨⟨⟨fixed.result.id,all.result⟩,count.result.1,lanes.result⟩,priced+lanes.steps+7⟩

theorem emit_keeps_header {m key prec b d : ℕ} (J : J6R26DescriptorTree.Job (rootHalfWidth m) b d prec)
    (issue : Meter (Word key)) (gate : Stamp key prec) (pad : ℕ) :
    let Y := emitLanes J issue gate pad
    Y.result.header=(J.make issue).result ∧ Y.result.selected=(selectPorts J.group J.ports).result ∧
      Y.steps=(J.make issue).steps+
        (J6R12CollisionEdges.mapMeter (birthLanes m pad gate ⟨issue.result,J.precision⟩) Y.result.selected).steps+7 :=
  ⟨rfl,rfl,rfl⟩

private theorem meter_map_of_map {X A B : Type*} (f : A→Meter B) (g : X→A) (xs : List X) :
    J6R12CollisionEdges.mapMeter f (xs.map g)=J6R12CollisionEdges.mapMeter (f∘g) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons,J6R12CollisionEdges.mapMeter,ih,Function.comp_apply]

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)

noncomputable abbrev rootParent := (makeTypedRootParent G X.source ell X.centre).result

noncomputable def outerLanes (gate : Stamp key prec) (pad : ℕ) : Meter (ExteriorLanes m key prec pad) :=
  let input := (rootPreparationFor X).result.parents
  let J := externalHeaderJob (b:=edgew) X.address.marked X.birth (word (q:=1) 0) input
  emitLanes J X.issue gate pad

noncomputable def actualLane (gate : Stamp key prec) (pad : ℕ) (h : Port (RootWire m)) :
    RootLanes m key prec pad :=
  rootLaneSpec m pad gate (X.seed pad).immutable.payload.stamp (side h)
    (physicalSeatField (rootChart T) (oddAxis m) (residentPageKey m) (edge h))

theorem actual_outer_stamp (pad : ℕ) :
    (X.seed pad).immutable.payload.stamp=⟨X.issue.result,X.birth⟩ := by
  change Stamp.mk X.header.result.id X.birth=_
  rw [(stable_exterior_header X).1]

theorem outer_selected_input (gate : Stamp key prec) (pad : ℕ) :
    (outerLanes X gate pad).result.selected=((rootParent X).physicalSelected X.group).map (rootParent X).record := by
  let P := rootParent X
  let J := externalHeaderJob (b:=edgew) X.address.marked X.birth (word (q:=1) 0)
    (rootPreparationFor X).result.parents
  have gp : X.address.group=word X.group.val :=
    (valued_word X.address.group).symm.trans (congrArg word X.groupOK)
  have raw : (rootPreparationFor X).result.parents=P.raw :=
    (actual_shared_parent_file G X.source ell X.field X.hq X.copies X.pre X.centre).1
  change (emitLanes J X.issue gate pad).result.selected=_
  rw [(emit_keeps_header J X.issue gate pad).2.1]
  change (selectPorts X.address.group (rootPreparationFor X).result.parents).result=_
  rw [gp,raw]
  exact P.physical_port_select X.group

theorem actual_outer_header (gate : Stamp key prec) (pad : ℕ) :
    (outerLanes X gate pad).result.header=(X.seed pad).entry.result := by
  let J := externalHeaderJob (b:=edgew) X.address.marked X.birth (word (q:=1) 0)
    (rootPreparationFor X).result.parents
  have f := (emit_keeps_header J X.issue gate pad).1
  change (emitLanes J X.issue gate pad).result.header=X.header.result
  exact f.trans (shared_header_is_literal X).1.symm

#print axioms emit_keeps_header
#print axioms actual_outer_stamp
#print axioms outer_selected_input
#print axioms actual_outer_header
end J6R37StructuredRoot