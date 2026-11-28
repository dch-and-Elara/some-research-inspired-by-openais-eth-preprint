import J6R114SelectedOperandsAlign
import J6R108FinalDriverPaidSetup

/-! First and next issuers are constructed, not extra promises on the
selected group. The actual R55 first emitter and measured selected
dispatch are both run by the R102 metered native-code machine. -/
namespace J6R114SelectedOperands
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R9Recursive J6R50SourceProducer J6R51Online J6R52FreshExterior
open J6R57PublicRequest J6R54PublicFamily J6R22Active
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables J6R28GeneratedRootFrame
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R55CachedLedger J6R56PrintedExponent J6R49Cost J6R16ModeCost J6R10Reachable
open J6R62ActivePrep J6R64Active J6R66Active J6R66.BootPeak J6R57Public
open J6R67UnifiedRate J6R68ActiveInputs J6R68ActiveInputs.Sweep J6R57ScopeFee
open J6R108FinalDriver
open J6R68RateJoint.RootWords

open J6R75OuterTime J6R14ZeroMode J6R55Public
open J6R102NativeCodeMeter J6R92NativeWidth J6R55TerminalBootJoined J6R55BootBodies
open J6R55TerminalOrigin J6R53OldOwnerRoot J6R54ExteriorOwner J6R54TerminalBoot

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4900
set_option maxHeartbeats 8500000
set_option pp.maxSteps 1100
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
variable (pad : ℕ)
variable (prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
variable {rate : ℕ}
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
variable {T : Prepared G.bounds (G.selector ell) (exteriorChild G ell i j g) (literalSite W D i j g).hf}

local instance ackOperandsDecision :
    DecidableEq (J6R10Reachable.Envelope (N (G.selector ell)) (Childs (G.selector ell)) ((exteriorChild G ell i j g))) :=
  J6R24MeteredRecursion.sourceDecision (G.selector ell) (exteriorChild G ell i j g)

variable {ownerWidth rank : ℕ} {rootName : SourceVertex P→Word ownerWidth}
variable (gate : Stamp (KeyWidth kp tc tj) prec)
variable (root : RootRoster (P:=P) gate pad rootName)


/-- The remaining physical inputs to this one address, before
assembling the R55 selectors or generating any lane/seat file. -/
structure RawSelectedSources
    (Y : StableExterior G ell q rr cc dd edgew tc tj (KeyWidth kp tc tj) prec tw bw)
    (F : Prepared G.bounds (G.selector ell) (exteriorChild G ell Y.centre Y.sample Y.group) Y.hf)
    (rate : ℕ) where
  handles : FirstHandleSource (T:=F) Y pad
  owners : (lane : BootLaneTape Y gate pad) →
    Meter (FirstOwnerSources Y gate pad root (firstWriterFromActualBook Y gate pad handles lane))
  operators : OnlineOperators F (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate
  request : ∀ {v : Ticket (G.selector ell) (exteriorChild G ell Y.centre Y.sample Y.group)}
    (X : StoredSite F v (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
    (w : (Plan (G.selector ell)).Slot v.child), Meter (FixedRequest X w)

/-- Carry the actual held descriptor and bank, the complete source
acquisition meter, and the physical first/demand input records. -/
structure PublicOperandReceipt
    (T : Prepared G.bounds (G.selector ell) (exteriorChild G ell i j g)
      (literalSite W D i j g).hf) (rate : ℕ) where
  observed : StableExterior G ell q rr cc dd edgew tc tj (KeyWidth kp tc tj) prec tw bw
  same : observed=literalSite W D i j g
  bank : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)
  live : IsLive (observed.seed pad) bank
  own : OwnsHeader observed.header.result bank
  sourceImports : Meter (RawSelectedSources pad gate root observed
    (preparedAtOtherSource observed (literalSite W D i j g) same T) rate)
  actual : HeldR55Operands observed gate pad root
    (preparedAtOtherSource observed (literalSite W D i j g) same T) rate

variable (rootInj : Function.Injective rootName)
variable (sync : prior.synced)
variable (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)

variable (Y : StableExterior G ell q rr cc dd edgew tc tj (KeyWidth kp tc tj) prec tw bw)
variable (same : Y=literalSite W D i j g)
variable (source :
  (b : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)) →
  OwnsHeader Y.header.result b →
  Meter (RawSelectedSources pad gate root Y (preparedAtOtherSource Y (literalSite W D i j g) same T) rate))
variable (bank : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
variable (ack : (submitResidentRow D S pad prior (sourceRow (W:=W) D i j g)).result=some (bank,true))

/-- Attach to an already paid descriptor. The existing acknowledgment
is evidence about the supplied bank, not an instruction to publish
again. No re-reading of the descriptor occurs inside this function. -/
def assembleAfterActualAck : Meter (PublicOperandReceipt (W:=W) D pad i j g gate root T rate) :=
  let accepted := actual_public_return_owns_its_literal_seed_and_header D S pad prior i j g sync reserved bank ack
  have live : IsLive (Y.seed pad) bank := by rw [same]; exact accepted.1
  have owned : OwnsHeader Y.header.result bank := by rw [same]; exact accepted.2
  let acquired := source bank owned
  let I := acquired.result
  let phys := operandsOnTheHeldAndLiveExterior Y gate pad root I.handles I.owners I.operators I.request bank live rootInj
  ⟨⟨Y,same,bank,live,owned,acquired,phys.result⟩,acquired.steps+phys.steps+3⟩

theorem ack_assembly_carries_the_actual_descriptor_and_returned_bank :
    let built := assembleAfterActualAck D S pad prior i j g gate root rootInj sync reserved Y same source bank ack
    built.result.observed=Y ∧ built.result.bank=bank ∧
      built.result.sourceImports=source bank built.result.own := ⟨rfl,rfl,rfl⟩

/-- Export the original R108 ABI without recreating the physical source.
All producer values remain available in the original receipt. -/
def operandsForRegisteredAddress (R : PublicOperandReceipt (W:=W) D pad i j g gate root T rate) :
    SelectedR55Operands (W:=W) D pad i j g gate root T rate :=
  let held := reindexHeldOperandData R.observed (literalSite W D i j g) gate pad root R.same T R.actual
  ⟨held.bodyMachine,held.firstBodies,held.firstOwners,held.demandSource⟩

def projectRegisteredOperandMeter (out : Meter (PublicOperandReceipt (W:=W) D pad i j g gate root T rate)) :
    Meter (SelectedR55Operands (W:=W) D pad i j g gate root T rate) :=
  ⟨operandsForRegisteredAddress (W:=W) D pad i j g gate root out.result,out.steps⟩

theorem registration_keeps_the_full_production_fee
    (out : Meter (PublicOperandReceipt (W:=W) D pad i j g gate root T rate)) :
    (projectRegisteredOperandMeter (W:=W) D pad i j g gate root out).steps=out.steps := rfl

#print axioms assembleAfterActualAck
#print axioms ack_assembly_carries_the_actual_descriptor_and_returned_bank
#print axioms operandsForRegisteredAddress
#print axioms registration_keeps_the_full_production_fee
end
end J6R114SelectedOperands

