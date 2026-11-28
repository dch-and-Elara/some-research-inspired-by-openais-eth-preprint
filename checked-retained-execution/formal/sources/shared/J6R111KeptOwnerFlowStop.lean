import J6R111KeptOwnerFlowNext
import J6R57PublicNoChartLeaf

/-! Positive stopping from the genuinely entered state. No provider
dictionary, no second resident install and no subsequent reconstruction
of the live stack appear in this evaluator. -/
namespace J6R111KeptOwnerFlow
open scoped Classical Polynomial
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R58LeafScale J6R62Leaf J6R27OriginalGate J6R36ChildFramedRoute J6R54TerminalBoot
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R52Terminal J6R53TerminalGate J6R53OldOwner J6R49SourceLayout J6R66LeafTariff J6R65LeafRate
open J6R52CacheWhole J6R51ParentFrames J6R82LayoutDebit J6R82LeafTime
open J6R9Recursive J6R58LeafScale J6R16ModeCost J6R14LayoutCost J6R68ActiveInputs
open V8NativeMessage.N2DLabels J6R10Repack J6R94HeldOwnerProvider J6R110ScopeWordRates
open J6R30ProducedGateRegistry J6R66Active J6R64Active J6R68.RecursivePeak J6R54PeakInput J6R59Public
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 25000000
set_option maxRecDepth 5500
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
variable (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))
variable (A : CapturedEntry X p w Y)
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (gate : Stamp key prec)
variable (boot : ExactPrintedBoot X M gate)

def resumePositive :
    Meter (Block (T.frame (Path.step p w).reached) ell×PageBank f ell key prec tw bw (pageKeyWidth m+pad)) :=
  let out := readPositiveHere X p w Y A
  ⟨(out.result,A.bank),out.steps⟩

include boot in
theorem positive_continuation_reads_the_exact_live_bank_and_decodes_the_true_leaf
    (same : Y=sourceState M p w) (gateWidth : gate.created.val=base)
    (basePos : 0<base) (positive : 0<((Plan sel).child c w).edges)
    (outer : IsLive (X.seed pad) A.bank) (stack : opened (borns M) (IsLive (X.seed pad)) (.step p w) A.bank) :
    let out := resumePositive X p w Y A
    (T.frame (Path.step p w).reached).decode out.result.1=
      reduce (p.ticket w).child.prec f ell ((p.ticket w).child.host.contract X.hf) ∧
      out.result.2=A.bank := by
  subst Y
  let site := sourceState M p w
  let inps := readKeptStopTapes X p w site (bindKept X p w site A.labelled A.resident)
  let F := T.frame (Path.step p w).reached
  obtain ⟨word,hit,decoded⟩ := actual_owner_terminal_correct_without_legacy_chart X M gate boot
    p w inps F A.bank gateWidth basePos positive (IsLive (X.seed pad)) outer stack
  refine ⟨?_,rfl⟩
  change F.decode (finishOwnerAttempt F (executeOwnerTerminal X p w site inps F A.bank)).result=_
  unfold finishOwnerAttempt
  rw [hit]
  exact decoded

section SuccessorStack
variable (u : (Plan sel).Slot (p.ticket w).child)
variable (K : Meter (HeldOwnerLoad Y (u:=u) (gateHistory T (bootGates X) p)))
variable (cache : CachedParentFrames Y.site)

theorem published_successor_bank_is_the_actual_R65_current_stack
    (actual : Y=sourceState M p w)
    (load : HEq K.result.load (M.demand (sourceState M p w) u).result)
    (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad)) :
    let next := (produceCacheSidecarOnce K.result.load cache).result.next
    afterOne (stackBank (borns M) initial (.step p w)) next.birth.job=
      stackBank (borns M) initial (.step (.step p w) u) := by
  dsimp only
  rw [made_successor_on_the_exact_selected_load_is_the_next_R66_source X p w Y u K cache M actual load]
  rfl
end SuccessorStack

#print axioms positive_continuation_reads_the_exact_live_bank_and_decodes_the_true_leaf
#print axioms published_successor_bank_is_the_actual_R65_current_stack
end
end J6R111KeptOwnerFlow

