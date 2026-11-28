import J6R55BootBodiesLanes
import J6R48RawRouteLiteral

/-! Generate a complete legal first native physical file. It retapes
the same original R37 lane under the R48 ancestry address and the
real first-slot packing's group word, without an old body field. -/
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
open J6R48RawRoute J6R11Blueprint J1PPrinted J6R24MeteredRecursion
set_option quotPrecheck false
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18500000
set_option maxRecDepth 3400
set_option Elab.async false
noncomputable section

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "E" => ((exteriorChild G ell X.centre X.sample X.group).host.Edge)
variable (gate : Stamp key prec) (pad : ℕ)

def bootRow {a₀ b : ℕ} (seat : E→SeatField a₀ b) (h : Port E) : PortRow (rootHalfWidth m+1) :=
  match h with
  | .inl e=>nextPortView false (seat e).rowGroup (laneView X gate pad e).gate
  | .inr e=>nextPortView true (seat e).colGroup (laneView X gate pad e).packet

theorem boot_row_body_is_initialPayload {a₀ b : ℕ} (seat : E→SeatField a₀ b) (h : Port E) :
    (bootRow X gate pad seat h).body=(initialPayload X gate pad h).2 := by
  cases h <;> rfl

theorem boot_row_address {a₀ b : ℕ} (seat : E→SeatField a₀ b) (h : Port E) :
    (bootRow X gate pad seat h).address=
      childHalfKey ((rootParent X).record (edge h).val).address (side h) := by
  cases h <;> rfl

theorem boot_row_distinct {a₀ b : ℕ} (seat : E→SeatField a₀ b) :
    Function.Injective (fun h=> (bootRow X gate pad seat h).address) := by
  intro p h same
  change (bootRow X gate pad seat p).address=(bootRow X gate pad seat h).address at same
  rw [boot_row_address,boot_row_address] at same
  have bits : (((rootParent X).record (edge p).val).address,side p)=
      (((rootParent X).record (edge h).val).address,side h) := child_half_key_injective same
  have eq : edge p=edge h := Subtype.val_injective
    ((rootParent X).distinct (congrArg Prod.fst bits))
  have b := congrArg Prod.snd bits
  cases p <;> cases h
  · exact congrArg Sum.inl eq
  · exact Bool.noConfusion b
  · exact Bool.noConfusion b
  · exact congrArg Sum.inr eq

def bootRaw {a₀ b : ℕ} (L : BootLaneTape X gate pad)
    (source : Meter (List (SeatField a₀ b))) :
    Meter (Option (List (PortRow (rootHalfWidth m+1)))) :=
  let W := writeBootRows L.run.result source.result
  ⟨W.result,source.steps+W.steps+4⟩

theorem boot_raw_receipt {a₀ b : ℕ} (L : BootLaneTape X gate pad)
    (source : Meter (List (SeatField a₀ b))) (seat : E→SeatField a₀ b)
    (trueSource : source.result=(orderedExteriorEdges X).map seat) :
    let out := bootRaw X gate pad L source
    out.result=some ((pairedPorts (orderedExteriorEdges X)).map (bootRow X gate pad seat)) ∧
    out.steps=source.steps+8+
      ((orderedExteriorEdges X).map (fun e=>bootPairFee (laneView X gate pad e) (seat e))).sum := by
  have A := written_boot_rows_exact (orderedExteriorEdges X) (laneView X gate pad) seat
  let W := writeBootRows L.run.result source.result
  have shape : W.result=some ((orderedExteriorEdges X).flatMap (fun e=>bootPairRows (laneView X gate pad e) (seat e))) := by
    unfold W
    rw [L.exact,trueSource]
    exact A.1
  have same : (pairedPorts (orderedExteriorEdges X)).map (bootRow X gate pad seat)=
      (orderedExteriorEdges X).flatMap (fun x=>bootPairRows (laneView X gate pad x) (seat x)) := by
    rw [pairedPorts,List.map_flatMap]
    rfl
  refine ⟨shape.trans (congrArg some same.symm),?_⟩
  have cost : W.steps=4+((orderedExteriorEdges X).map
      (fun e=>bootPairFee (laneView X gate pad e) (seat e))).sum := by
    unfold W
    rw [L.exact,trueSource]
    exact A.2
  change source.steps+W.steps+4=_
  rw [cost]
  omega

variable {s : ℕ}
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable (d : J6R12Blueprint.Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) (exteriorChild G ell X.centre X.sample X.group))
variable (t : Center (printedParams (f:=f) (ell:=ell) s) (exteriorChild G ell X.centre X.sample X.group))
local notation "A" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) (exteriorChild G ell X.centre X.sample X.group).depth)

structure TerminalSeats (b : ℕ) where
  code : P11FullPacking.Page A (packing sel d).copies (Fin 64)→Word b
  made : Meter (List (SeatField A b))
  exact : made.result=(orderedExteriorEdges X).map (physicalSeatField (packing sel d) (centerIndex d t) code)

variable {sel d t} {b : ℕ}

def readFirstPhysical (L : BootLaneTape X gate pad) (S : TerminalSeats X sel d t b) :
    Meter (PhysicalPorts sel d t (rootHalfWidth m+1)) :=
  let seat := physicalSeatField (packing sel d) (centerIndex d t) S.code
  let out := bootRaw X gate pad L S.made
  let order := pairedPorts (orderedExteriorEdges X)
  let receipt := boot_raw_receipt X gate pad L S.made seat S.exact
  ⟨⟨out.result.getD [],order,paired_ports_nodup _ (reviewed_exterior_order X).1,
    (fun h=>(mem_paired_ports h _).mpr ((reviewed_exterior_order X).2 (edge h))),
    bootRow X gate pad seat,by rw [receipt.1]; rfl,
    (fun h=>by
      cases h with
      | inl e=>exact literal_seat_names_group (packing sel d) (centerIndex d t) S.code (.inl e)
      | inr e=>exact literal_seat_names_group (packing sel d) (centerIndex d t) S.code (.inr e)),
    boot_row_distinct X gate pad seat⟩,out.steps⟩

theorem actual_first_physical_is_written (L : BootLaneTape X gate pad) (S : TerminalSeats X sel d t b)
    (h : Port E) :
    let out := readFirstPhysical X gate pad L S
    let seat := physicalSeatField (packing sel d) (centerIndex d t) S.code
    out.result.order=pairedPorts (orderedExteriorEdges X) ∧
    (out.result.record h).body=(initialPayload X gate pad h).2 ∧
    (out.result.record h).address=childHalfKey ((rootParent X).record (edge h).val).address (side h) ∧
    out.steps=S.made.steps+8+
      ((orderedExteriorEdges X).map (fun e=>bootPairFee (laneView X gate pad e) (seat e))).sum :=
  ⟨rfl,boot_row_body_is_initialPayload X gate pad _ h,boot_row_address X gate pad _ h,
    (boot_raw_receipt X gate pad L S.made _ S.exact).2⟩

#print axioms boot_row_body_is_initialPayload
#print axioms boot_row_distinct
#print axioms boot_raw_receipt
#print axioms readFirstPhysical
#print axioms actual_first_physical_is_written
end
end J6R55BootBodies
