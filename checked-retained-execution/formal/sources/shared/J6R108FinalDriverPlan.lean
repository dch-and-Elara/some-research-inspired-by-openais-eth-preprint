import J6R108FinalDriverLegal
import J6R68ActiveInputsSweepPhysical
import J6R68AbsolutePrescribedSeed
import J6R67UnifiedRateLeaf

/-! Build the selected group plan using a bank value actually returned
by the literal request. Its Ready field is derived from the two actual
issued meters. The same native R102 body, true source owner callback
and existing R68 selected layout are the ones installed in the plan. -/
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
open J6R75OuterTime J6R14ZeroMode J6R55Public J6R68AbsolutePrescribed
open J6R102NativeCodeMeter J6R92NativeWidth J6R55TerminalBootJoined J6R55BootBodies
open J6R55TerminalOrigin J6R53OldOwnerRoot J6R54ExteriorOwner J6R54TerminalBoot

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4900
set_option maxHeartbeats 11000000
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

local instance planDecision :
    DecidableEq (J6R10Reachable.Envelope (N (G.selector ell)) (Childs (G.selector ell)) ((exteriorChild G ell i j g))) :=
  J6R24MeteredRecursion.sourceDecision (G.selector ell) (exteriorChild G ell i j g)

variable {ownerWidth rank : ℕ} {rootName : SourceVertex P→Word ownerWidth}
variable (gate : Stamp (KeyWidth kp tc tj) prec)
variable (root : RootRoster (P:=P) gate pad rootName)
variable (baseMachine : OnlineMachine T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate)
variable (A : FirstBodyProgram (literalSite W D i j g) gate pad T)
variable (owners : OwnerWordsAtBodies (literalSite W D i j g) gate pad root A)
variable (rootInj : Function.Injective rootName)

variable (basePos : 0<base)
variable (edgeOrder : Fin (exteriorChild G ell i j g).edges ≃ (exteriorChild G ell i j g).host.Edge)
variable (stopInput : OwnerInputProvider (T:=T) (pad:=pad) (literalSite W D i j g))

/-- The body and the immutable published bank are explicit inputs to
this function. In particular it is suitable inside the actual
admission continuation, not a recipe to replay the installation. -/
def planFromTheActualReturnedBank
    (bank : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
    (live : IsLive ((literalSite W D i j g).seed pad) bank)
    (sync : prior.synced) (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)
    (old : ∀ row∈prior.headers,row.id.val ≤ D.mark.val) (capacity : nativeDepthCapacity W D i j g)
    (first : ∀ w : (Plan (G.selector ell)).Slot ((exteriorChild G ell i j g)),
      (A.old w).result.issued=issuedAtFirstDepth W D i j g)
    (next : ∀ {v : Ticket (G.selector ell) ((exteriorChild G ell i j g))}
      (Y : StoredSite T v (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
      (w : (Plan (G.selector ell)).Slot v.child),
      (baseMachine.demand Y w).result.event.issued=increment Y.birth.job.identifier)
    (ack : (submitResidentRow D S pad prior ((sourceRow (W:=W) D i j g))).result=some (bank,true))
    (gateWidth : gate.created.val=base) (baseFit : base ≤ 2*physicalSize m native)
    (seen : HasMeasuredOwnerInputs (literalSite W D i j g)
      (paidCodeAtReturnedBank D pad i j g gate root baseMachine A owners rootInj bank live) stopInput)
    (selected : CurrentLayoutSources T (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rank (literalSite W D i j g).header.result)
    (fit : ∀ {c : Call (PhysicalHost f ell)} (p : Path (G.selector ell) ((exteriorChild G ell i j g)) c) (a : ((printedParams (f:=f) (ell:=ell) (physicalSize m native))).cutoff<c.edges),
      InputFits (G.selector ell) (readyAtPath T p a) rate)
    (chart : MountedChart T)
    {pointerWidth : ℕ} (tails : SavedDirectoryTails pointerWidth) :
    RawGroupPlan D S pad prior ((sourceRow (W:=W) D i j g)) G.bounds rate (rank+1) := by
  let current := paidCodeAtReturnedBank D pad i j g gate root baseMachine A owners rootInj bank live
  let machine := withPaidOwnerLeaves (literalSite W D i j g) current basePos edgeOrder stopInput
  have ready : ReadyOnStack (borns current) bank := by
    intro c p w
    exact this_paid_native_code_driver_is_ready D S pad prior i j g gate root baseMachine A owners rootInj
      bank live sync reserved old capacity first next ack p w
  have eqBank := the_actual_R57_reply_is_the_proof_only_published_snapshot D S pad prior i j g
    sync reserved bank ack
  have born : ReadyOnStack (borns machine) bank := by
    intro c p w
    exact replacing_leaves_preserves_actual_ready_stack (literalSite W D i j g) current basePos edgeOrder stopInput
      bank (fun {_} p w=>ready p w) p w
  have boot : ExactPrintedBoot (literalSite W D i j g) current gate :=
    metered_selected_boot_still_has_the_exact_printed_bodies (literalSite W D i j g) gate pad A root baseMachine owners bank live rootInj
  have leaves : LeafAgreement machine bank :=
    same_source_terminal_agrees_without_LoopCharts (literalSite W D i j g) current basePos edgeOrder stopInput gate boot
      bank gateWidth live (fun {_} p w=>ready p w) seen
  have readyOnIndex : ReadyOnStack (borns machine) (publishedBank D S pad prior ((sourceRow (W:=W) D i j g))) := by
    rw [← eqBank]
    intro c p w
    exact born p w
  have leavesOnIndex : LeafAgreement machine (publishedBank D S pad prior ((sourceRow (W:=W) D i j g))) := by
    rw [← eqBank]
    exact leaves
  exact {
    sel := G.selector ell
    prep := T
    machine := machine
    keep := selected.retained fit
    chart := chart
    layout := fun b own level=>(selected.exterior b own level).run
    retire := retireSavedDirectory tails
    valid := fun {_} p w=>readyOnIndex p w
    leaves := leavesOnIndex
    entrance := original_prescribed_exterior_seed G ell i j g baseFit }

#print axioms planFromTheActualReturnedBank
end
end J6R108FinalDriver

