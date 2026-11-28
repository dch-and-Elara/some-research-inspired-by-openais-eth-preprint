import J6R114SelectedOperandsBoot
import J6R55PublicDrivers

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
open J6R55Public J6R51Online
open J6R53OldOwner J6R55TerminalOrigin J6R32ChildResidentTransfer J6R50SourceProducer

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
local instance heldOperandDecision : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) (Ext)) :=
  J6R24MeteredRecursion.sourceDecision sel Ext
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

variable {own : ℕ} {rootName : SourceVertex P→Word own}
variable (root : RootRoster (P:=P) gate pad rootName)


variable {rate : ℕ}

/-- The actual shared source values, retained by reference for the
chosen binder. Their production is charged by the outer maker. -/
structure KeptFirstInputs (H : FirstHandleSource (T:=T) X pad) where
  lanes : BootLaneTape X gate pad
  ownerBook : Meter (FirstOwnerSources X gate pad root (firstWriterFromActualBook X gate pad H lanes))

/-- Same executable fields as R108's printed-address record, together
with the actual held source values. No complete successor or positive
terminal certificate is a field. -/
structure HeldR55Operands (T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf)
    (rate : ℕ) where
  firstHandles : FirstHandleSource (T:=T) X pad
  firstFetched : KeptFirstInputs X gate pad root firstHandles
  bodyMachine : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate
  firstBodies : FirstBodyProgram X gate pad T
  firstOwners : OwnerWordsAtBodies X gate pad root firstBodies
  demandSource : ∀ {v : Ticket sel (exteriorChild G ell X.centre X.sample X.group)}
    (Y : StoredSite T v key prec tw bw (pageKeyWidth m+pad))
    (w : (Plan sel).Slot v.child), Meter (FixedRequest Y w)

variable (H : FirstHandleSource (T:=T) X pad)
variable (owners : (lane : BootLaneTape X gate pad) →
  Meter (FirstOwnerSources X gate pad root (firstWriterFromActualBook X gate pad H lane)))
variable (ops : OnlineOperators T key prec tw bw (pageKeyWidth m+pad) rate)
variable (req : ∀ {v : Ticket sel (exteriorChild G ell X.centre X.sample X.group)}
    (Y : StoredSite T v key prec tw bw (pageKeyWidth m+pad))
    (w : (Plan sel).Slot v.child), Meter (FixedRequest Y w))
variable (bank : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (live : IsLive (X.seed pad) bank) (rootInj : Function.Injective rootName)

/-- Install the actual R55 callbacks with the returned resident bank,
rather than taking a fully formed reference OnlineMachine. The
R55/R68 per-slot meters are not added to this assembly again. -/
def operandsOnTheHeldAndLiveExterior : Meter (HeldR55Operands X gate pad root T rate) :=
  let lane := freshBootLaneTape X gate pad
  let fetched := owners lane
  let A := firstWriterFromActualBook X gate pad H lane
  let Q := ownerWordsFromActualTables X gate pad root A
    (actual_first_writer_uses_the_original_receiving_order X gate pad H lane) fetched.result
  let boot := fun w =>
    assembleFirstExterior X gate pad root w
      (joinedSlots X gate pad root A Q w) bank live rootInj
  let M := fromActualInputMeters ops boot req
  ⟨⟨H,⟨lane,fetched⟩,M,A,Q,req⟩,lane.run.steps+fetched.steps+4+4⟩

theorem paid_exterior_operands_use_the_recipient_bank_and_exact_body
    (w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group)) :
    let A := operandsOnTheHeldAndLiveExterior X gate pad root H owners ops req bank live rootInj
    A.result.bodyMachine.initial w =
      assembleFirstExterior X gate pad root w (joinedSlots X gate pad root
        A.result.firstBodies A.result.firstOwners w) bank live rootInj := rfl

theorem actual_exterior_operands_demand_calls_the_same_measured_request
    {v : Ticket sel (exteriorChild G ell X.centre X.sample X.group)}
    (Y : StoredSite T v key prec tw bw (pageKeyWidth m+pad)) (w : (Plan sel).Slot v.child) :
    let A := operandsOnTheHeldAndLiveExterior X gate pad root H owners ops req bank live rootInj
    A.result.bodyMachine.demand Y w=meteredSelectedDemand (req Y w) := rfl

theorem physical_operand_assembly_pays_shared_operands_once :
    let A := operandsOnTheHeldAndLiveExterior X gate pad root H owners ops req bank live rootInj
    let L := freshBootLaneTape X gate pad
    A.steps=L.run.steps+(owners L).steps+4+4 := rfl

theorem physical_operand_packet_carries_the_whole_measured_owner_input :
    let A := operandsOnTheHeldAndLiveExterior X gate pad root H owners ops req bank live rootInj
    A.result.firstFetched.ownerBook=owners (freshBootLaneTape X gate pad) := rfl

#print axioms physical_operand_packet_carries_the_whole_measured_owner_input
#print axioms operandsOnTheHeldAndLiveExterior
#print axioms paid_exterior_operands_use_the_recipient_bank_and_exact_body
#print axioms actual_exterior_operands_demand_calls_the_same_measured_request
#print axioms physical_operand_assembly_pays_shared_operands_once
end
end J6R114SelectedOperands

