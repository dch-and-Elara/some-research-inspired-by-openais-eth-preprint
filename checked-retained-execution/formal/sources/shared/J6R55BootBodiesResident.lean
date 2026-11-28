import J6R55BootBodiesOccurrence
import J6R52CacheSourceReplay
import J6R33GeneratedChildSiteSparse

/-! Reuse the actual resident seat array when its order is the same
as the selected original half-port order. A merely complete greedy
order is not asserted equal; in that case the already charged
ordinal export may be used instead. -/
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
open J6R48RawRoute J6R11Blueprint J1PPrinted J6R24MeteredRecursion J6R50SourceProducer
open J6R52CacheSource J6R33GeneratedChildSite
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 23000000
set_option maxRecDepth 3900
set_option Elab.async false
noncomputable section

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "E" => ((exteriorChild G ell X.centre X.sample X.group).host.Edge)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))
local notation "first" => ((Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group) (exteriorChild G ell X.centre X.sample X.group)).ticket w)
local notation "Pg" => (pageKeyWidth m+pad)
local notation "A" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) (exteriorChild G ell X.centre X.sample X.group).depth)

def actualSameOrderSeats (I : OccurrenceInput T first key prec tw bw Pg)
    (order : I.geometry.edges=orderedExteriorEdges X) :
    TerminalSeats X sel (ticketReady T first) (first).centerAt ((I.q-A)+13*A) :=
  ⟨childPageKey (I.q-A),⟨I.physical.result.seats,0⟩,by rw [I.geometry.seats,order]; rfl⟩

theorem actual_same_order_seats_no_second_preparation
    (I : OccurrenceInput T first key prec tw bw Pg)
    (order : I.geometry.edges=orderedExteriorEdges X) (L : BootLaneTape X gate pad)
    (h : Port E) :
    let P := readFirstPhysical X gate pad L (actualSameOrderSeats X pad w I order)
    (P.result.record h).body=(initialPayload X gate pad h).2 ∧
    P.steps=8+((orderedExteriorEdges X).map (fun e=>
      bootPairFee (laneView X gate pad e)
        (physicalSeatField (packing sel (ticketReady T first))
          (centerIndex (ticketReady T first) (first).centerAt) (childPageKey (I.q-A)) e))).sum := by
  have h₀ := actual_first_physical_is_written X gate pad L (actualSameOrderSeats X pad w I order) h
  exact ⟨h₀.2.1,h₀.2.2.2⟩

variable {b : ℕ}

def terminalSeatsFromPaidExport
    (code : P11FullPacking.Page A (packing sel (ticketReady T first)).copies (Fin 64)→Word b)
    (alignedRead : Meter (Option (List (SeatField A b))))
    (fits : alignedRead.result=some ((orderedExteriorEdges X).map
      (physicalSeatField (packing sel (ticketReady T first))
        (centerIndex (ticketReady T first) (first).centerAt) code))) :
    TerminalSeats X sel (ticketReady T first) (first).centerAt b :=
  have found : alignedRead.result.isSome := by rw [fits]; rfl
  ⟨code,unwrapSuccess alignedRead found,congrArg Meter.result (unwrap_success_exact alignedRead found _ fits)⟩

theorem paid_seat_export_is_not_free
    (code : P11FullPacking.Page A (packing sel (ticketReady T first)).copies (Fin 64)→Word b)
    (alignedRead : Meter (Option (List (SeatField A b))))
    (fits : alignedRead.result=some ((orderedExteriorEdges X).map
      (physicalSeatField (packing sel (ticketReady T first))
        (centerIndex (ticketReady T first) (first).centerAt) code))) :
    (terminalSeatsFromPaidExport (T:=T) X w code alignedRead fits).made.steps=alignedRead.steps :=
  rfl

#print axioms actualSameOrderSeats
#print axioms actual_same_order_seats_no_second_preparation
#print axioms terminalSeatsFromPaidExport
#print axioms paid_seat_export_is_not_free
end
end J6R55BootBodies
