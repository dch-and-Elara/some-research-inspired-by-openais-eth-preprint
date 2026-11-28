import J6R111KeptOwnerFlowStop

/-! Charge the actual captured positive leaf. No extra provider, second
terminal interpreter or legacy whole-run clock is included. -/
namespace J6R114RetainedTerminalTariff
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
open J6R51ParentFrames J6R65LeafRate J6R82LeafTime J6R24MeteredRecursion
open J6R111KeptOwnerFlow
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 28000000
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
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (A : CapturedEntry X p w (sourceState M p w))

def measuredInputFromCapture : Meter (OwnerTerminalInput X p w (sourceState M p w)) :=
  readKeptStopTapes X p w (sourceState M p w) (bindKept X p w (sourceState M p w) A.labelled A.resident)

theorem retained_positive_steps_use_the_same_terminal_on_the_live_stack
    (initial : (PageBank f ell key prec tw bw (pageKeyWidth m+pad))) (bank : A.bank=stackBank (borns M) initial (.step p w)) :
    (resumePositive X p w (sourceState M p w) A).steps =
      (readProvidedOnR65Bank X M p w (measuredInputFromCapture X p w M A) initial).steps := by
  unfold resumePositive readPositiveHere readProvidedOnR65Bank measuredInputFromCapture
  dsimp only
  rw [bank]

variable (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate)

include boot in
theorem actual_retained_leaf_pays_its_real_tape_copies_and_terminal
    (gateWidth : gate.created.val=base) (basePos : 0<base) (positive : 0<(p.ticket w).child.edges)
    (outer : IsLive (X.seed pad) A.bank)
    (inside : opened (borns M) (IsLive (X.seed pad)) (.step p w) A.bank) :
    let K := measuredInputFromCapture X p w M A
    let saved := mountResident (sourceState M p w) A.resident
    let a := A.labelled
    let headers := groupHeadersFromOwnedRaw (sourceState M p w) (gateHistory T (bootGates X) p) A.owners
      a.input a.ingress a.units a.raw.rawView a.axis a.law
    let terminal := meteredTerminalFromOwners (sourceState M p w) K.result.saved K.result.headers.raw K.result.roster.raw
      (p.ticket w).child.edges (T.frame (Path.step p w).reached) A.bank
    ∃ word, terminal.result=some word ∧
      resumePositive X p w (sourceState M p w) A =
        ⟨(word,A.bank),saved.steps+headers.steps+terminal.steps+12⟩ := by
  let K := measuredInputFromCapture X p w M A
  let saved := mountResident (sourceState M p w) A.resident
  let a := A.labelled
  let headers := groupHeadersFromOwnedRaw (sourceState M p w) (gateHistory T (bootGates X) p) A.owners
    a.input a.ingress a.units a.raw.rawView a.axis a.law
  let terminal := meteredTerminalFromOwners (sourceState M p w) K.result.saved K.result.headers.raw K.result.roster.raw
    (p.ticket w).child.edges (T.frame (Path.step p w).reached) A.bank
  let op := executeOwnerTerminal X p w (sourceState M p w) K (T.frame (Path.step p w).reached) A.bank
  obtain ⟨word,hit,_⟩ := actual_owner_terminal_correct_without_legacy_chart X M gate boot
    p w K (T.frame (Path.step p w).reached) A.bank gateWidth basePos positive (IsLive (X.seed pad)) outer inside
  have run : op=⟨terminal.result,K.steps+terminal.steps+4⟩ :=
    owner_terminal_is_the_metered_reader X p w (sourceState M p w) K (T.frame (Path.step p w).reached) A.bank
  have core : terminal.result=some word := (congrArg Meter.result run).symm.trans hit
  have inFee : K.steps=saved.steps+headers.steps+5 := rfl
  have opFee : op.steps=K.steps+terminal.steps+4 := congrArg Meter.steps run
  refine ⟨word,core,?_⟩
  change (⟨((finishOwnerAttempt (T.frame (Path.step p w).reached) op).result,A.bank),(finishOwnerAttempt (T.frame (Path.step p w).reached) op).steps⟩ :
    Meter _) = ⟨(word,A.bank),saved.steps+headers.steps+terminal.steps+12⟩
  have yes : op.result=some word := hit
  simp only [finishOwnerAttempt,yes]
  exact congrArg (Meter.mk (word,A.bank)) (by rw [opFee,inFee]; omega)

#print axioms retained_positive_steps_use_the_same_terminal_on_the_live_stack
#print axioms actual_retained_leaf_pays_its_real_tape_copies_and_terminal
end
end J6R114RetainedTerminalTariff
