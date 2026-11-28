import J6R110ScopeWordRatesPositive
import J6R108FinalDriverConfigured

namespace J6R110ScopeWordRates
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
variable (handoff : PaidKeptHandoff (T:=T) (pad:=pad) (literalSite W D i j g))

/-- This is precisely the `seen` field expected by R108, on its
actual selected pre-stop machine and returned physical bank. No
new plan or replacement demand implementation is introduced. -/
theorem configured_R108_accepts_the_actual_kept_positive_provider
    (received : ActualPositiveArrival (literalSite W D i j g)
      (selectedPublicBeforeStopAtReturn D pad i j g gate root baseMachine A owners rootInj request bank live)
      handoff) :
    HasMeasuredOwnerInputs (literalSite W D i j g)
      (selectedPublicBeforeStopAtReturn D pad i j g gate root baseMachine A owners rootInj request bank live)
      (keptTapeOwnerProvider (literalSite W D i j g) handoff) :=
  actual_paid_kept_arrivals_imply_the_existing_success_field _ _ _ received

variable (basePos : 0<base)
variable (edgeOrder : Fin (exteriorChild G ell i j g).edges ≃ (exteriorChild G ell i j g).host.Edge)

/-- The selected actual stopped callback invokes the literal R94
input reader on that same source occurrence/bank. The actual arrival
and reader fee, including the handoff, are both present. -/
theorem configured_R108_positive_stop_runs_the_paid_kept_reader
    {c : Call (PhysicalHost f ell)} (p : Path (G.selector ell) (exteriorChild G ell i j g) c)
    (w : (Plan (G.selector ell)).Slot c)
    (stop : ((Plan (G.selector ell)).child c w).edges≤
      (printedParams (f:=f) (ell:=ell) (physicalSize m native)).cutoff)
    (positive : 0<((Plan (G.selector ell)).child c w).edges)
    (L : LiveKeptStopTapes (literalSite W D i j g) p w
      (sourceState (selectedPublicBeforeStopAtReturn D pad i j g gate root baseMachine A owners rootInj request bank live) p w))
    (charge : ℕ)
    (arrived : handoff p w
      (sourceState (selectedPublicBeforeStopAtReturn D pad i j g gate root baseMachine A owners rootInj request bank live) p w)
      stop=Meter.mk (some L) charge) :
    let X := literalSite W D i j g
    let M := selectedPublicBeforeStopAtReturn D pad i j g gate root baseMachine A owners rootInj request bank live
    let source := actualStoppedInputFromKeptTapes X M p w L.resident L.owners L.names L.input L.ingress L.units L.raw L.axisBytes L.sameChart
    let charged := Meter.mk source.result (charge+source.steps+3)
    readLeaf (withPaidOwnerLeaves X M basePos edgeOrder (keptTapeOwnerProvider X handoff)) bank (.step p w) stop=
      readProvidedOnR65Bank X M p w charged bank :=
  stopped_actual_machine_uses_the_literal_kept_reader_and_handoff_charge _ _ p w handoff stop L charge
    arrived basePos edgeOrder bank positive

#print axioms configured_R108_accepts_the_actual_kept_positive_provider
#print axioms configured_R108_positive_stop_runs_the_paid_kept_reader
end
end J6R110ScopeWordRates