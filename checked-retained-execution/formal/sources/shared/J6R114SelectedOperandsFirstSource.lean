import J6R114SelectedOperandsAdmission
import J6R102NativeCodeMeterJoined
import J6R111KeptOwnerFlowRunRoot

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
open J6R108FinalDriver J6R111KeptOwnerFlow
open J6R68RateJoint.RootWords

open J6R75OuterTime J6R14ZeroMode J6R55Public
open J6R102NativeCodeMeter J6R92NativeWidth J6R55TerminalBootJoined J6R55BootBodies
open J6R55TerminalOrigin J6R53OldOwnerRoot J6R54ExteriorOwner J6R54TerminalBoot

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4900
set_option maxHeartbeats 2600000
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

local instance localHeldCodeDecision :
    DecidableEq (J6R10Reachable.Envelope (N (G.selector ell)) (Childs (G.selector ell)) ((exteriorChild G ell i j g))) :=
  J6R24MeteredRecursion.sourceDecision (G.selector ell) (exteriorChild G ell i j g)

variable {ownerWidth rank : ℕ} {rootName : SourceVertex P→Word ownerWidth}
variable (gate : Stamp (KeyWidth kp tc tj) prec)
variable (root : RootRoster (P:=P) gate pad rootName)



variable (rootInj : Function.Injective rootName)
variable (sync : prior.synced)
variable (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)


variable (R : PublicOperandReceipt (W:=W) D pad i j g gate root T rate)

/-- Preserve the observed descriptor in the actual R102 machine. Its
first and downstream roster scans keep their original measured prices.
No installed atlas, handle table or owner tape is acquired here again. -/
def machineOnHeldOperandsWithRealCode :
    OnlineMachine (preparedAtOtherSource R.observed (literalSite W D i j g) R.same T)
      (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate :=
  withMeteredNativeCode R.observed gate pad R.actual.firstBodies root R.actual.bodyMachine
    R.actual.firstOwners R.bank R.live rootInj

/-- This producer returns both the exact installed first site and the
complete owner spool used by that same R102 first-slot call. -/
def firstOwnerSourceOnTheSameHeldOperands :
    FirstSource R.observed (machineOnHeldOperandsWithRealCode D pad i j g gate root rootInj R) where
  make w := assembleFirstExteriorKeepingOwners R.observed w gate root
    (measuredSlots R.observed gate pad R.actual.firstBodies root R.actual.firstOwners w)
    R.bank R.live rootInj
  exact w := retaining_first_owners_projects_to_the_whole_literal_R55_meter R.observed w gate root
    (measuredSlots R.observed gate pad R.actual.firstBodies root R.actual.firstOwners w)
    R.bank R.live rootInj

theorem held_machine_demand_runs_the_actual_source_then_the_paid_code
    {v : Ticket (G.selector ell) (exteriorChild G ell R.observed.centre R.observed.sample R.observed.group)}
    (Y : StoredSite (preparedAtOtherSource R.observed (literalSite W D i j g) R.same T) v
      (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)) (w : (Plan (G.selector ell)).Slot v.child) :
    (machineOnHeldOperandsWithRealCode D pad i j g gate root rootInj R).demand Y w=
      (R.actual.bodyMachine.demand Y w).bind measureLocalLoad := rfl

theorem held_machine_has_the_actual_printed_boot :
    ExactPrintedBoot R.observed (machineOnHeldOperandsWithRealCode D pad i j g gate root rootInj R) gate :=
  metered_selected_boot_still_has_the_exact_printed_bodies R.observed gate pad
    R.actual.firstBodies root R.actual.bodyMachine R.actual.firstOwners R.bank R.live rootInj

#print axioms machineOnHeldOperandsWithRealCode
#print axioms firstOwnerSourceOnTheSameHeldOperands
#print axioms held_machine_demand_runs_the_actual_source_then_the_paid_code
#print axioms held_machine_has_the_actual_printed_boot
end
end J6R114SelectedOperands

