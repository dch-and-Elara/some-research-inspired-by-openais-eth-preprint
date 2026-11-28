import J6R55BootBodiesBits
import J6R41StructuredAllPathsExterior
import J6R37StructuredRootFields
import J6R55BootBodiesOrder

/-! The exterior ordered edge list comes from the original checked
root half-port filter. The actual boot writer can consume the already
resident root tape, without publishing a second copy of the seed
and without guessing a lineage body. -/
namespace J6R55BootBodies
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R26DescriptorTree J6R35RootOrigins J6R36ChildFramedRoute
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34RootAtlas J6R41StructuredAllPaths
open J6Mesh J6OrientedHost J6R24LegalLayout J6R10Repack J6R12Blueprint
open J6R12Repack J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic
open J6R32ChildResidentTransfer J6R27OriginalGate J6R33StatefulArithmeticPage
open J6R37StructuredRoot J6R30GeneratedRootLayout J6R25PreparedSupply
open J6R48RawRoute
set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18500000
set_option maxRecDepth 3500
set_option Elab.async false
noncomputable section

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co d edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co d edgew tc tj key prec tw bw)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "E" => ((Ext).host.Edge)

def laneView (gate : Stamp key prec) (pad : ℕ) (e : E) : RootLanes m key prec pad :=
  actualLane X gate pad e.val

theorem true_r37_emitted_lane_order (gate : Stamp key prec) (pad : ℕ) :
    (outerLanes X gate pad).result.lanes=(orderedExteriorEdges X).map (laneView X gate pad) := by
  let A := outerLanes X gate pad
  let D := rootParent X
  let f₀ := birthLanes m pad gate ⟨X.issue.result,X.birth⟩
  have proofRead : A.result.lanes=(J6R12CollisionEdges.mapMeter f₀ A.result.selected).result := rfl
  have read (e : E) :
      f₀ (D.record e.val)=⟨laneView X gate pad e,J6R37StructuredRoot.laneFee m pad key prec⟩ :=
    source_lane_row_paid X gate pad e.val
  have actual := original_lane_batch_exact f₀ (fun e : E=>D.record e.val)
    (laneView X gate pad) (J6R37StructuredRoot.laneFee m pad key prec) (orderedExteriorEdges X) read
  change A.result.lanes=_
  rw [proofRead,show A.result.selected=_ from outer_selected_input X gate pad,
    exterior_order_is_exactly_selected X,List.map_map]
  exact congrArg Meter.result actual

theorem exterior_half_tape_is_parent_file :
    (makeHalfTape m [] X.source.raw).result=(rootParent X).raw :=
  ((generated_typed_parent_receipt G X.source ell X.centre).1).symm

/-- A reader of already available root physical bytes. It is only
a filter and a lane writer: no directory lookup or atlas publication
is performed here. -/
def putBootLanes (gate : Stamp key prec) (pad : ℕ)
    (raw : List (PortRow (rootHalfWidth m))) : Meter (List (RootLanes m key prec pad)) :=
  let selected := selectPorts X.address.group raw
  let out := J6R12CollisionEdges.mapMeter (birthLanes m pad gate ⟨X.issue.result,X.birth⟩) selected.result
  ⟨out.result,selected.steps+out.steps+4⟩

theorem put_real_boot_lanes (gate : Stamp key prec) (pad : ℕ)
    (raw : List (PortRow (rootHalfWidth m))) (same : raw=(rootParent X).raw) :
    let M := putBootLanes X gate pad raw
    M.result=(orderedExteriorEdges X).map (laneView X gate pad) ∧
    M.result=(outerLanes X gate pad).result.lanes ∧
    M.steps=3+(raw.map rowScanFee).sum+(J6R37StructuredRoot.laneFee m pad key prec+6)*(orderedExteriorEdges X).length+4 := by
  let D := rootParent X
  let f₀ := birthLanes m pad gate ⟨X.issue.result,X.birth⟩
  have g : X.address.group=word X.group.val :=
    (valued_word X.address.group).symm.trans (congrArg word X.groupOK)
  have ordered : (selectPorts X.address.group raw).result=(orderedExteriorEdges X).map (fun e=>D.record e.val) := by
    rw [same,g,D.physical_port_select,exterior_order_is_exactly_selected X,List.map_map]
    rfl
  have laneJob := original_lane_batch_exact f₀ (fun e : E=>D.record e.val)
    (laneView X gate pad) (J6R37StructuredRoot.laneFee m pad key prec) (orderedExteriorEdges X)
      (fun e=>source_lane_row_paid X gate pad e.val)
  have feeSel := (select_ports_exact X.address.group raw).2
  let W := putBootLanes X gate pad raw
  have ready : W.result=(orderedExteriorEdges X).map (laneView X gate pad) := by
    change (J6R12CollisionEdges.mapMeter f₀ (selectPorts X.address.group raw).result).result=_
    rw [ordered,laneJob]
  refine ⟨ready,ready.trans (true_r37_emitted_lane_order X gate pad).symm,?_⟩
  change (selectPorts X.address.group raw).steps+
    (J6R12CollisionEdges.mapMeter f₀ (selectPorts X.address.group raw).result).steps+4=_
  rw [feeSel,ordered,laneJob]

structure BootLaneTape (gate : Stamp key prec) (pad : ℕ) where
  run : Meter (List (RootLanes m key prec pad))
  exact : run.result=(orderedExteriorEdges X).map (laneView X gate pad)

def alreadyEmittedBootLanes (gate : Stamp key prec) (pad : ℕ) : BootLaneTape X gate pad :=
  let old := outerLanes X gate pad
  ⟨⟨old.result.lanes,old.steps⟩,true_r37_emitted_lane_order X gate pad⟩

def bootLanesFromRead (gate : Stamp key prec) (pad : ℕ)
    (raw : Meter (List (PortRow (rootHalfWidth m)))) (same : raw.result=(rootParent X).raw) :
    BootLaneTape X gate pad :=
  let out := putBootLanes X gate pad raw.result
  ⟨⟨out.result,raw.steps+out.steps⟩,(put_real_boot_lanes X gate pad raw.result same).1⟩

def freshBootLaneTape (gate : Stamp key prec) (pad : ℕ) : BootLaneTape X gate pad :=
  bootLanesFromRead X gate pad (makeHalfTape m [] X.source.raw) (exterior_half_tape_is_parent_file X)

theorem actual_fresh_lane_file_and_fee (gate : Stamp key prec) (pad : ℕ) :
    let L := freshBootLaneTape X gate pad
    let half := makeHalfTape m [] X.source.raw
    L.run.result=(outerLanes X gate pad).result.lanes ∧
    L.run.steps=half.steps+3+(half.result.map rowScanFee).sum+
      (J6R37StructuredRoot.laneFee m pad key prec+6)*(orderedExteriorEdges X).length+4 := by
  let half := makeHalfTape m [] X.source.raw
  have law := put_real_boot_lanes X gate pad half.result (exterior_half_tape_is_parent_file X)
  refine ⟨law.2.1,?_⟩
  change half.steps+(putBootLanes X gate pad half.result).steps=_
  rw [law.2.2]
  dsimp only [half]
  omega

#print axioms true_r37_emitted_lane_order
#print axioms put_real_boot_lanes
#print axioms actual_fresh_lane_file_and_fee
end
end J6R55BootBodies
