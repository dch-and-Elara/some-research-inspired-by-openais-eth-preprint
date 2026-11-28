import J6R108FinalDriverProfile
import J6R108FinalDriverCapacity
import J6R110ScopeWordRatesPositiveR108
import J6R110CanonicalCoverageMount

/-! First and next issuers are constructed, not extra promises on the
selected group. The actual R55 first emitter and measured selected
dispatch are both run by the R102 metered native-code machine. -/
namespace J6R108FinalDriver
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
open J6R102FinalPhase J6R79Numeric J6R110ScopeWordRates
open J6R110CanonicalCoverage J6R110CanonicalMount J6R109CanonicalProbeTable
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

local instance actualRawGroupDecision :
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

variable (basePos : 0<base)
variable (edgeOrder : Fin (exteriorChild G ell i j g).edges ≃ (exteriorChild G ell i j g).host.Edge)

variable (K producerPower leafPower : ℕ) (coefficients : ProducerCoefficients)
variable (handoff : PaidKeptHandoff (T:=T) (pad:=pad) (literalSite W D i j g))

/-- This refinement of the configured group uses the actual stopped
R94 owner reader and the emitted full original probe chart. It does
not infer that those retained owner records arrive merely from path
geometry, nor drop their producer's charge. -/
def groupPhaseFromActualKeptArrivalAndChart
    (bank : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
    (live : IsLive ((literalSite W D i j g).seed pad) bank)
    (sync : prior.synced) (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)
    (old : ∀ row∈prior.headers,row.id.val ≤ D.mark.val)
    (lowRoom : D.mark.val+pathLimit (physicalSize m native) 2 ≤ 2^kp)
    (ack : (submitResidentRow D S pad prior (sourceRow (W:=W) D i j g)).result=some (bank,true))
    (gateWidth : gate.created.val=base) (baseFit : base ≤ 2*physicalSize m native)
    (received : ActualPositiveArrival (literalSite W D i j g)
      (selectedPublicBeforeStopAtReturn D pad i j g gate root baseMachine A owners rootInj request bank live)
      handoff)
    (bytes : (canonicalTable f.natDegree (fullProbeDegree f.natDegree+1)).result =
      OldOrderedBytes f.natDegree (fullProbeDegree f.natDegree) (full_probe_fit f.natDegree))
    (recipe : MeasuredProfile (T:=T) (rank:=rank) (literalSite W D i j g)
      (selectedPublicBeforeStopAtReturn D pad i j g gate root baseMachine A owners rootInj request bank live)
      basePos edgeOrder (keptTapeOwnerProvider (literalSite W D i j g) handoff)
      (publishedBank D S pad prior (sourceRow (W:=W) D i j g))
      (published_head_is_the_actual_raw_header D S pad prior (sourceRow (W:=W) D i j g))
      K producerPower leafPower coefficients) :
    Σ Q : RawGroupPlan D S pad prior (sourceRow (W:=W) D i j g) G.bounds rate (rank+1),
      SelectedPlanSource D S pad prior (sourceRow (W:=W) D i j g) Q K producerPower leafPower coefficients :=
  chosenGroupAndItsActualPhaseSource D S pad prior i j g gate root baseMachine A owners rootInj request
    basePos edgeOrder (keptTapeOwnerProvider (literalSite W D i j g) handoff) K producerPower leafPower coefficients
    bank live sync reserved old (path_limit_fits_every_actual_public_address D i j g lowRoom)
    ack gateWidth baseFit
    (configured_R108_accepts_the_actual_kept_positive_provider D pad i j g gate root baseMachine A
      owners rootInj request bank live handoff received)
    recipe (mountFullChart T bytes)

#print axioms groupPhaseFromActualKeptArrivalAndChart
end
end J6R108FinalDriver

