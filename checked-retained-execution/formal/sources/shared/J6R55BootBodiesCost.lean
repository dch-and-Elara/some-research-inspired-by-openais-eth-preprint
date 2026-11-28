import J6R55BootBodiesPhysical

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

def bootCopyStride (m a₀ b : ℕ) : ℕ :=
  8*rootHalfWidth m+3*pageKeyWidth m+6*a m+3*a₀+3*b+79

theorem actual_boot_lane_lengths {m key prec pad : ℕ} (old born : Stamp key prec) (side₀ : Bool)
    (F : SeatField (a m) (pageKeyWidth m)) :
    let L := rootLaneSpec m pad old born side₀ F
    L.gate.body.length=1+pageKeyWidth m+a m ∧ L.packet.body.length=2+a m := by
  change (false::(F.page.bits++F.slot.bits)).length=_ ∧
    (true::side₀::F.slot.bits).length=_
  simp only [List.length_cons,List.length_append,F.page.size,F.slot.size]
  omega

theorem exact_stride_of_actual_lane {a₀ b : ℕ} (seat : E→SeatField a₀ b) (e : E) :
    bootPairFee (laneView X gate pad e) (seat e)=bootCopyStride m a₀ b := by
  have general := actual_boot_lane_lengths (pad:=pad) gate (X.seed pad).immutable.payload.stamp (side e.val)
    (physicalSeatField (rootChart P) (oddAxis m) (residentPageKey m) (edge e.val))
  have aGate : (laneView X gate pad e).gate.body.length=1+pageKeyWidth m+a m := general.1
  have aPacket : (laneView X gate pad e).packet.body.length=2+a m := general.2
  unfold bootPairFee bootCopyStride nextPortFee
  rw [aGate,aPacket]
  omega

theorem actual_boot_body_copy_uniform_fee {a₀ b : ℕ} (L : BootLaneTape X gate pad)
    (source : Meter (List (SeatField a₀ b))) (seat : E→SeatField a₀ b)
    (trueSource : source.result=(orderedExteriorEdges X).map seat) :
    (bootRaw X gate pad L source).steps=
      source.steps+8+(orderedExteriorEdges X).length*bootCopyStride m a₀ b := by
  rw [(boot_raw_receipt X gate pad L source seat trueSource).2]
  have eq : ((orderedExteriorEdges X).map (fun e=>bootPairFee (laneView X gate pad e) (seat e)))=
      (orderedExteriorEdges X).map (fun _=>bootCopyStride m a₀ b) := by
    apply List.map_congr_left
    intro e _
    exact exact_stride_of_actual_lane X gate pad seat e
  simp only [eq,List.map_const',List.sum_replicate,nsmul_eq_mul,Nat.cast_id]

#print axioms actual_boot_lane_lengths
#print axioms exact_stride_of_actual_lane
#print axioms actual_boot_body_copy_uniform_fee
end
end J6R55BootBodies
