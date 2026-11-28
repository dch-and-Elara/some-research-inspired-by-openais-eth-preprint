import J6R68RateJointRootWordsOnlineProgram
import J6R64BootSeatsProvider
import J6R55TerminalBootJoinedCore

/-! A selected least-mode-code runtime and its actual paid scanner
do not change the first or later issuers. Use only same-result facts
to prove ownership/readiness; the additional R102 fees are untouched. -/
namespace J6R114SelectedOperands
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R26DescriptorTree
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R34RootAtlas
open J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R24MeteredRecursion J6R51Online J6R50SourceProducer J6R49SourceLayout
open J6R30ProducedGateRegistry J6R57ScopeFee
open J6R55BootBodies J6R55TerminalOrigin J6R48GeneratedAddons
open J6Mesh J6OrientedHost J6R24LegalLayout J6R31RootResidentTables
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R32RootGeneratedRegistryInputs
open J6R35RootOrigins J6R55TerminalBootJoined J6R53OldOwnerRoot J6R54TerminalBoot J6R54ExteriorOwner
open J6R16ModeCost J6R68RateJoint.RootWords J6R64.BootSeats J6R48RawRoute J6R48GeneratedAddons
open J6R36ChildFramedRoute J6R53OldOwner J6R55TerminalOrigin J6R32ChildResidentTransfer J6R50SourceProducer

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 4900
set_option maxHeartbeats 8500000
set_option maxSynthPendingDepth 12

noncomputable section
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
local notation "Ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Pg" => (pageKeyWidth m+pad)
local instance bootOperandDecision : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) (Ext)) :=
  J6R24MeteredRecursion.sourceDecision sel Ext
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

variable {own : ℕ} {rootName : SourceVertex P→Word own}
variable (root : RootRoster (P:=P) gate pad rootName)

local notation "RootSlot" => ((Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group))

/-- The addressed book contains actual selected first-occurrence data,
not a materialized list of all slots. Its meter remains in A.old. -/
structure FirstHandleSource where
  make : ∀ w : RootSlot, Meter (FirstSlotBook (r:=exteriorChild G ell X.centre X.sample X.group)
    (sel:=sel) T key prec tw bw (pageKeyWidth m+pad) w)
  order : ∀ w : RootSlot, (make w).result.datum.geometry.edges=orderedExteriorEdges X

def firstWriterFromActualBook (H : FirstHandleSource (T:=T) X pad)
    (lane : BootLaneTape X gate pad) : FirstBodyProgram X gate pad T :=
  firstBodiesFromSelectedHandles X gate pad lane H.make H.order

theorem first_writer_loads_the_exact_paid_selected_book (H : FirstHandleSource (T:=T) X pad)
    (lane : BootLaneTape X gate pad) (w : RootSlot) :
    (firstWriterFromActualBook X gate pad H lane).old w=
      loadSelectedFirst (T:=T) (w:=w) (H.make w) X.issue.result := rfl

theorem actual_first_writer_uses_the_original_receiving_order
    (H : FirstHandleSource (T:=T) X pad) (lane : BootLaneTape X gate pad)
    (w : RootSlot) :
    ((firstWriterFromActualBook X gate pad H lane).old w).result.geometry.edges=
      orderedExteriorEdges X :=
  selected_first_receiving_order X pad H.make H.order w

/-- These are the actual owner name/key data and the per-slot paid
query tape. The seat table itself is not supplied. The typed tape also
does not promise that a retained positive-leaf owner roster arrived. -/
structure FirstOwnerSources (A : FirstBodyProgram X gate pad T) where
  width : RootSlot→ℕ
  name : ∀ w : RootSlot, (Ext).host.Row⊕(Ext).host.Col→Word (width w)
  distinct : ∀ w, Function.Injective (name w)
  keys : ∀ w, KeyInputs X gate pad root (name w)
  queryTape : ∀ w, Meter (OwnerTape (bodyAtActualSlot X gate pad A w).result (name w))
  fallback : ∀ w : RootSlot, Addon (width w)
    (dim ((Path.root : Path sel (Ext) (Ext)).ticket w)) key prec (pageKeyWidth m+pad)

def ownerWordsFromActualTables (A : FirstBodyProgram X gate pad T)
    (agree : ∀ w : RootSlot,(A.old w).result.geometry.edges=orderedExteriorEdges X)
    (U : FirstOwnerSources X gate pad root A) :
    OwnerWordsAtBodies X gate pad root A where
  width := U.width
  name := U.name
  distinct := U.distinct
  keys := U.keys
  ports w :=
    let I := (bodyAtActualSlot X gate pad A w).result
    have physical : I.native.result.physical.order=pairedPorts (orderedExteriorEdges X) := rfl
    have held : I.geometry.edges=(A.old w).result.geometry.edges := rfl
    let paired := physical.trans (congrArg pairedPorts ((held.trans (agree w)).symm))
    bootProvider I (U.name w) paired (U.queryTape w) (U.fallback w)

/-- One real lane build on the held descriptor, one owner source
setup, and no per-slot replay or query generation before its use. -/
def firstOperandsOnActualExterior (H : FirstHandleSource (T:=T) X pad)
    (owners : (lane : BootLaneTape X gate pad) →
      Meter (FirstOwnerSources X gate pad root (firstWriterFromActualBook X gate pad H lane))) :
    Meter (Σ A : FirstBodyProgram X gate pad T, OwnerWordsAtBodies X gate pad root A) :=
  let lane := freshBootLaneTape X gate pad
  let tape := owners lane
  let A := firstWriterFromActualBook X gate pad H lane
  let data := ownerWordsFromActualTables X gate pad root A
    (actual_first_writer_uses_the_original_receiving_order X gate pad H lane) tape.result
  ⟨⟨A,data⟩,lane.run.steps+tape.steps+4⟩

theorem actual_first_operand_set_pays_lane_setup_and_no_replay
    (H : FirstHandleSource (T:=T) X pad)
    (owners : (lane : BootLaneTape X gate pad) →
      Meter (FirstOwnerSources X gate pad root (firstWriterFromActualBook X gate pad H lane))) :
    let lane := freshBootLaneTape X gate pad
    let R := firstOperandsOnActualExterior X gate pad root H owners
    R.steps=lane.run.steps+(owners lane).steps+4 ∧
      (∀ w : RootSlot, R.result.1.old w=loadSelectedFirst (T:=T) (w:=w) (H.make w) X.issue.result) :=
  ⟨rfl,fun _=>rfl⟩

theorem selected_owner_query_and_seat_remain_in_their_actual_slot
    (H : FirstHandleSource (T:=T) X pad)
    (owners : (lane : BootLaneTape X gate pad) →
      Meter (FirstOwnerSources X gate pad root (firstWriterFromActualBook X gate pad H lane)))
    (w : RootSlot) :
    let lane := freshBootLaneTape X gate pad
    let U := firstOperandsOnActualExterior X gate pad root H owners
    let I := (bodyAtActualSlot X gate pad U.result.1 w).result
    (U.result.2.ports w).seats.steps =
      ((owners lane).result.queryTape w).steps+(canonicalSeatBank I).steps+3 := rfl

#print axioms first_writer_loads_the_exact_paid_selected_book
#print axioms actual_first_writer_uses_the_original_receiving_order
#print axioms ownerWordsFromActualTables
#print axioms firstOperandsOnActualExterior
#print axioms actual_first_operand_set_pays_lane_setup_and_no_replay
#print axioms selected_owner_query_and_seat_remain_in_their_actual_slot
end
end J6R114SelectedOperands

