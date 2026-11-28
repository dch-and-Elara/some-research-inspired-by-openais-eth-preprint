import J6R111KeptOwnerFlowLiteralFirst
import J6R108FinalDriverConfigured

namespace J6R111KeptOwnerFlow
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
open J6R75OuterTime J6R14ZeroMode J6R55Public
open J6R102NativeCodeMeter J6R92NativeWidth J6R55TerminalBootJoined J6R55BootBodies
open J6R55TerminalOrigin J6R53OldOwnerRoot J6R54ExteriorOwner J6R54TerminalBoot
open J6R108FinalDriver J6R94HeldOwnerProvider

set_option autoImplicit false

set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4900
set_option maxHeartbeats 10000000
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

local instance keptConfiguredDecision :
    DecidableEq (J6R10Reachable.Envelope (N (G.selector ell)) (Childs (G.selector ell)) ((exteriorChild G ell i j g))) :=
  J6R24MeteredRecursion.sourceDecision (G.selector ell) (exteriorChild G ell i j g)

variable {ownerWidth rank : ℕ} {rootName : SourceVertex P→Word ownerWidth}
variable (gate : Stamp (KeyWidth kp tc tj) prec)
variable (root : RootRoster (P:=P) gate pad rootName)
variable (baseMachine : OnlineMachine T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate)
variable (A : FirstBodyProgram (literalSite W D i j g) gate pad T)
variable (owners : OwnerWordsAtBodies (literalSite W D i j g) gate pad root A)
variable (rootInj : Function.Injective rootName)

variable (request : ∀ {v : Ticket (G.selector ell) ((exteriorChild G ell i j g))}
    (Y : StoredSite T v (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
    (w : (Plan (G.selector ell)).Slot v.child), Meter (FixedRequest Y w))

variable (bank : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
variable (live : IsLive ((literalSite W D i j g).seed pad) bank)
open J6R51Online J6R102NativeCodeMeter J6R55TerminalOrigin

/-- The native R102 slot compiler at this exact configured public
site returns its existing Meter and the actual full roster it used.
The old evaluator's projection is proved below. -/
def configuredFirstWithOwners
    (w : (Plan (G.selector ell)).Slot (exteriorChild G ell i j g)) :
    Meter (FirstSlotWithOwners (pad:=pad) (T:=T) (literalSite W D i j g) w) :=
  let X := literalSite W D i j g
  let firstBodies := publicIssuedBodyProgram W D i j g pad gate A
  let firstNames := ownerWordsWithPublicIssuer W D i j g pad gate root A owners
  let slot := measuredSlots X gate pad firstBodies root firstNames w
  assembleFirstExteriorKeepingOwners X w gate root slot bank live rootInj

theorem configured_R108_first_slot_projects_from_one_paid_full_roster
    (w : (Plan (G.selector ell)).Slot (exteriorChild G ell i j g)) :
    let K := configuredFirstWithOwners D pad i j g gate root A owners rootInj bank live w
    (⟨K.result.site,K.steps⟩ : Meter (StoredSite T
       ((Path.root : Path (G.selector ell) (exteriorChild G ell i j g) (exteriorChild G ell i j g)).ticket w)
        (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)))=
      (selectedPublicBeforeStopAtReturn D pad i j g gate root baseMachine A owners rootInj request bank live).initial w :=
  rfl

#print axioms configured_R108_first_slot_projects_from_one_paid_full_roster
end
end J6R111KeptOwnerFlow

