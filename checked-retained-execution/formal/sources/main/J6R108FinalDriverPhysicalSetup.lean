import J6R108FinalDriverPaidSetup
import J6R108FinalDriverReceivedExterior
import J6R108FinalDriverProfileIndex

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
open J6R102FinalPhase J6R79Numeric J6R110ScopeWordRates J6R111SelectedGroup J6R94ExteriorDebit
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

local instance physicalSetupGroupDecision :
    DecidableEq (J6R10Reachable.Envelope (N (G.selector ell)) (Childs (G.selector ell)) ((exteriorChild G ell i j g))) :=
  J6R24MeteredRecursion.sourceDecision (G.selector ell) (exteriorChild G ell i j g)

variable {ownerWidth rank : ℕ} {rootName : SourceVertex P→Word ownerWidth}
variable (gate : Stamp (KeyWidth kp tc tj) prec)
variable (root : RootRoster (P:=P) gate pad rootName)

variable (rootInj : Function.Injective rootName)
variable (basePos : 0<base)
variable (edgeOrder : Fin (exteriorChild G ell i j g).edges ≃ (exteriorChild G ell i j g).host.Edge)
variable (handoff : PaidKeptHandoff (T:=T) (pad:=pad) (literalSite W D i j g))
variable (sync : prior.synced) (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)
variable (acquire :
    (b : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)) →
    OwnsHeader (literalSite W D i j g).header.result b →
    Meter (SelectedR55Operands D pad i j g gate root T rate))


variable (K producerPower leafPower : ℕ) (coefficients : ProducerCoefficients)
local instance receivedGroupFiniteEdge : Fintype (exteriorChild G ell (literalSite W D i j g).centre (literalSite W D i j g).sample (literalSite W D i j g).group).host.Edge :=
  (exteriorChild G ell i j g).host.finiteEdge

/-- Export the actual R111 setup together with its R102 phase
certificate. The exterior R94 writer captures the received bank
and emitted word, the positive leaf uses the actually carried
R110 owner records, and the actual full chart is paid once. -/
def literalPaidSetupWithRealR94Exterior
    (data : SelectedR55Operands D pad i j g gate root T rate)
    (bank : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
    (live : IsLive ((literalSite W D i j g).seed pad) bank)
    (own : OwnsHeader (literalSite W D i j g).header.result bank)
    (acquired : (acquire bank own).result=data)
    (advanced : ∀ row∈prior.headers,row.id.val ≤ D.mark.val)
    (lowRoom : D.mark.val+pathLimit (physicalSize m native) 2 ≤ 2^kp)
    (ack : (submitResidentRow D S pad prior (sourceRow (W:=W) D i j g)).result=some (bank,true))
    (gateWidth : gate.created.val=base) (baseFit : base ≤ 2*physicalSize m native)
    (received : ActualPositiveArrival (literalSite W D i j g)
      (selectedPublicBeforeStopAtReturn D pad i j g gate root data.bodyMachine
        data.firstBodies data.firstOwners rootInj data.demandSource bank live) handoff)
    (bytes : (canonicalTable f.natDegree (fullProbeDegree f.natDegree+1)).result =
      OldOrderedBytes f.natDegree (fullProbeDegree f.natDegree) (full_probe_fit f.natDegree))
    (H : MeasuredProfile (T:=T) (rank:=rank) (literalSite W D i j g)
      (selectedPublicBeforeStopAtReturn D pad i j g gate root data.bodyMachine
        data.firstBodies data.firstOwners rootInj data.demandSource bank live)
      basePos edgeOrder (keptTapeOwnerProvider (literalSite W D i j g) handoff)
      bank own K producerPower leafPower coefficients)
    (stock : RootLayoutStock P rootName)
    (issued : Word (KeyWidth kp tc tj)) (sameWord : issued=(literalSite W D i j g).issue.result)
    (fits : Fintype.card (exteriorChild G ell (literalSite W D i j g).centre (literalSite W D i j g).sample (literalSite W D i j g).group).host.Edge<2^rank)
    (shape : RootOrderMatch (T:=T) (literalSite W D i j g) pad stock fits)
    (rootShape : letI := (exteriorChild G ell (literalSite W D i j g).centre (literalSite W D i j g).sample (literalSite W D i j g).group).host.finiteRow
                 letI := (exteriorChild G ell (literalSite W D i j g).centre (literalSite W D i j g).sample (literalSite W D i j g).group).host.finiteCol
                 LayoutScales shape.input rank K)
    (widths : ExteriorInputWidths (literalSite W D i j g) pad stock bank K)
    (rootBill : installedExteriorRawRoof K ≤ H.ingress) :
    Σ Q : RawGroupPlan D S pad prior (sourceRow (W:=W) D i j g) G.bounds rate (rank+1),
      SelectedPlanSource D S pad prior (sourceRow (W:=W) D i j g) Q K producerPower leafPower coefficients ×
      PaidSetupForPlan D S pad prior (sourceRow (W:=W) D i j g) Q := by
  let X := literalSite W D i j g
  let M := selectedPublicBeforeStopAtReturn D pad i j g gate root data.bodyMachine
    data.firstBodies data.firstOwners rootInj data.demandSource bank live
  let P1 := withActualR94ExteriorInTheMeasuredProfile X M basePos edgeOrder
    (keptTapeOwnerProvider X handoff) bank own H stock live issued sameWord fits shape rootShape widths rootBill
  let proofBank := publishedBank D S pad prior (sourceRow (W:=W) D i j g)
  have hsame : bank=proofBank :=
    the_actual_R57_reply_is_the_proof_only_published_snapshot D S pad prior i j g sync reserved bank ack
  let P2 := reindexMeasuredProfileAtTheSameReceivedBank X M basePos edgeOrder
    (keptTapeOwnerProvider X handoff) bank own P1 proofBank hsame
    (published_head_is_the_actual_raw_header D S pad prior (sourceRow (W:=W) D i j g))
  exact literalPaidSetupOnTheActualAcceptedBoundBank D S pad prior i j g gate root rootInj basePos edgeOrder
    handoff sync reserved acquire K producerPower leafPower coefficients data bank live own acquired
    advanced lowRoom ack gateWidth baseFit received bytes P2

#print axioms literalPaidSetupWithRealR94Exterior
end
end J6R108FinalDriver

