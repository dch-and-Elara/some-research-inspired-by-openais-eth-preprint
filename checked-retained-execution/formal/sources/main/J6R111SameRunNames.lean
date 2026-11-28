import J6R108FinalDriverConfigured
import J6R108FinalDriverHandoff
import J6R110CanonicalAllPeakRun
import J6R75OuterTimeGroup

/-! Check just the physical arguments of the already verified
Configured plan. The canonical chart is the same complete paid
chart's result; the admission-snapshot equality only transports
the bank index. No additional publication or mount is introduced. -/
namespace J6R111SameRunNames
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
open J6R108FinalDriver J6R110CanonicalCoverage J6R109CanonicalProbeTable J6R110CanonicalMount

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4900
set_option maxHeartbeats 18500000
set_option pp.maxSteps 2200
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
local instance sameRunDecision :
    DecidableEq (J6R10Reachable.Envelope (N (G.selector ell)) (Childs (G.selector ell)) (exteriorChild G ell i j g)) :=
  J6R24MeteredRecursion.sourceDecision (G.selector ell) (exteriorChild G ell i j g)

variable {ownerWidth rank : ℕ} {rootName : SourceVertex P→Word ownerWidth}
variable (gate : Stamp (KeyWidth kp tc tj) prec)
variable (root : RootRoster (P:=P) gate pad rootName)
variable (baseMachine : OnlineMachine T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate)
variable (A : FirstBodyProgram (literalSite W D i j g) gate pad T)
variable (owners : OwnerWordsAtBodies (literalSite W D i j g) gate pad root A)
variable (rootInj : Function.Injective rootName)
variable (request : ∀ {v : Ticket (G.selector ell) (exteriorChild G ell i j g)}
    (Y : StoredSite T v (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)) (w : (Plan (G.selector ell)).Slot v.child),
    Meter (FixedRequest Y w))
variable (basePos : 0<base) (edgeOrder : Fin (exteriorChild G ell i j g).edges ≃ (exteriorChild G ell i j g).host.Edge)
variable (stopInput : OwnerInputProvider (T:=T) (pad:=pad) (literalSite W D i j g))

theorem configured_core_is_the_literal_raw_core_of_the_paid_full_chart
    (bank : (PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))) (live : IsLive ((literalSite W D i j g).seed pad) bank)
    (sync : prior.synced) (reserved : ∀ y∈prior.headers,y.id.bits.take kp≠D.mark.bits)
    (old : ∀ row∈prior.headers,row.id.val≤D.mark.val) (capacity : nativeDepthCapacity W D i j g)
    (ack : (submitResidentRow D S pad prior (sourceRow (W:=W) D i j g)).result=some (bank,true))
    (gateWidth : gate.created.val=base) (baseFit : base≤2*physicalSize m native)
    (seen : HasMeasuredOwnerInputs (literalSite W D i j g)
      (selectedPublicBeforeStopAtReturn D pad i j g gate root baseMachine A owners rootInj request bank live)
      stopInput)
    (selected : CurrentLayoutSources T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rank (literalSite W D i j g).header.result)
    (fit : ∀ {c : Call (PhysicalHost f ell)} (p : Path (G.selector ell) (exteriorChild G ell i j g) c)
      (on : (printedParams (f:=f) (ell:=ell) (physicalSize m native)).cutoff<c.edges),
        InputFits (G.selector ell) (readyAtPath T p on) rate)
    (bytes : (canonicalTable f.natDegree (fullProbeDegree f.natDegree+1)).result=
      OldOrderedBytes f.natDegree (fullProbeDegree f.natDegree) (full_probe_fit f.natDegree))
    {pointerWidth : ℕ} (tails : SavedDirectoryTails pointerWidth) :
    let chart := mountFullChart T bytes
    let plan := selectedPrintedGroupFromActualReturn D S pad prior i j g gate root baseMachine A owners rootInj
      request basePos edgeOrder stopInput bank live sync reserved old capacity ack gateWidth baseFit seen
      selected fit chart.result tails
    let picked := selectedPublicBeforeStopAtReturn D pad i j g gate root baseMachine A owners rootInj request bank live
    let own := (actual_public_return_owns_its_literal_seed_and_header D S pad prior i j g sync reserved bank ack).2
    let raw := runRawPhysicalExterior (literalSite W D i j g) (withPaidOwnerLeaves (literalSite W D i j g) picked basePos edgeOrder stopInput)
      (selected.retained fit) chart.result (fun b h on=>(selected.exterior b h on).run) (retireSavedDirectory tails)
      bank own
    plan.chart=chart.result ∧
    runRawPhysicalExterior (actualExterior (W:=W) D (sourceRow (W:=W) D i j g)) plan.machine plan.keep plan.chart plan.layout plan.retire
      (publishedBank D S pad prior (sourceRow (W:=W) D i j g)) (published_head_is_the_actual_raw_header D S pad prior (sourceRow (W:=W) D i j g))=raw := by
  have same := the_actual_R57_reply_is_the_proof_only_published_snapshot D S pad prior i j g sync reserved bank ack
  subst bank
  exact ⟨rfl,rfl⟩


/-- The successful native continuation can be written as the very same
canonical wrapper plus the original selection charge. This equality
accounts for one chart Meter, not an invocation nested inside another. -/
theorem actual_ack_continuation_charges_one_chart_and_the_same_R110_run
    (choosePaid : (b : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)) →
      (submitResidentRow D S pad prior (sourceRow (W:=W) D i j g)).result=some (b,true) →
      OwnsHeader (literalSite W D i j g).header.result b →
      Meter (OnlineMachine T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate))
    {cw : ℕ} (F : RetainedAfter T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate cw)
    (layout : ExteriorLayout (T:=T) (page:=pageKeyWidth m+pad) (cw:=cw) (literalSite W D i j g))
    (retire : PageJob f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)→ℕ)
    (bytes : (canonicalTable f.natDegree (fullProbeDegree f.natDegree+1)).result=
      OldOrderedBytes f.natDegree (fullProbeDegree f.natDegree) (full_probe_fit f.natDegree))
    (b : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
    (ack : (submitResidentRow D S pad prior (sourceRow (W:=W) D i j g)).result=some (b,true) ∧
      OwnsHeader (literalSite W D i j g).header.result b) :
    let chart := mountFullChart T bytes
    let picked := choosePaid b ack.1 ack.2
    let native := runRawExteriorWithPaidCanonicalChart (literalSite W D i j g)
      (fullProbeDegree f.natDegree) (full_probe_fit f.natDegree) bytes
      (canonical_mount_coverage_from_original_prepared T) picked.result F layout retire b ack.2
    continueSelectedPublicGroup D S pad prior (sourceRow (W:=W) D i j g) (literalSite W D i j g)
      choosePaid F chart layout retire b ack=⟨native.result,picked.steps+native.steps⟩ := by
  let chart := mountFullChart T bytes
  let picked := choosePaid b ack.1 ack.2
  let run := runRawPhysicalExterior (literalSite W D i j g) picked.result F chart.result layout retire b ack.2
  change (⟨run.result,picked.steps+chart.steps+run.steps+3⟩ : Meter _) =
    ⟨run.result,picked.steps+(chart.steps+run.steps+3)⟩
  exact congrArg (Meter.mk run.result) (by omega)

#print axioms actual_ack_continuation_charges_one_chart_and_the_same_R110_run

#print axioms configured_core_is_the_literal_raw_core_of_the_paid_full_chart
end
end J6R111SameRunNames
