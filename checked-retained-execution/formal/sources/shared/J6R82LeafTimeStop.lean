import J6R82LeafTimeOrdered
import J6R65LeafRateNumerics

/-! Same-path stopped-leaf prices. The printed source exponent is unchanged.
The scalar uses actual encoded widths; these are not inferred from mere
value-equivalence of an arbitrary replacement chart. -/
namespace J6R82LeafTime
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R50Peak J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
open J6R57Public J6R58LeafScale J6R62Leaf J6R27OriginalGate J6R36ChildFramedRoute J6R54TerminalBoot
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R52Terminal J6R53TerminalGate J6R53OldOwner J6R49SourceLayout J6R66LeafTariff J6R65LeafRate
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 41000000
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
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable {c : Call (PhysicalHost f ell)}
variable (p : Path sel (exteriorChild G ell X.centre X.sample X.group) c)
variable (w : (Plan sel).Slot c)
local notation "ext" => (exteriorChild G ell X.centre X.sample X.group)
local notation "Bank" => (PageBank f ell key prec tw bw (pageKeyWidth m+pad))
local notation "Cmd" => (ReadCmd key (pageKeyWidth m+pad))
local notation "deg" => (4*Nat.clog 2 s)
local notation "ch" => (p.ticket w).child

variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (basePos : 0<base)
variable (ord : Fin (exteriorChild G ell X.centre X.sample X.group).edges≃
  (exteriorChild G ell X.centre X.sample X.group).host.Edge)
variable (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
variable (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate)
variable (gateWidth : gate.created.val=base)

def stoppedPreparationCoefficient (width ownerWidth body arity : ℕ) : ℕ :=
  printedPreparation (leafH s) (vertexCount (ext).host+4*(C*s)) (3*(C*s))
    width ownerWidth key prec (pageKeyWidth m+pad) (pageKeyWidth m+J6Mesh.a m) body arity

include boot gateWidth in
theorem positive_readLeaf_with_real_reader_and_explicit_provider
    (initial : Bank) (first : IsLive (X.seed pad) initial) (legal : ReadyOnStack (borns M) initial)
    (supply : HasMeasuredOwnerInputs X M ownerInputs)
    (hn : native≤m) (hs : s=physicalSize m native) (baseFit : base≤C*s)
    (stop : ((Plan sel).child c w).edges≤(printedParams (f:=f) (ell:=ell) s).cutoff)
    (positive : 0<((Plan sel).child c w).edges)
    {width ownerWidth body arity significant : ℕ}
    (enc : ActualEncodingFits (stackBank (borns M) initial (.step p w)) significant)
    (birthWord : (sourceState M p w).birth.port≤width)
    (ownerWord : (sourceState M p w).site.ownerWidth≤ownerWidth)
    (payloadWidths : ∀ (A : OwnerTerminalInput X p w (sourceState M p w)),
      (ownerInputs p w (sourceState M p w) stop).result=some A →
      observedFrameWidth A.saved.rows≤body ∧ observedGateWidth A.roster.raw≤arity) :
    let Y := sourceState M p w
    let path := Path.step p w
    let B := stackBank (borns M) initial path
    let L := readLeaf (withPaidOwnerLeaves X M basePos ord ownerInputs) initial path stop
    let prep := stoppedPreparationCoefficient (pad:=pad) (s:=s) (C:=C) X width ownerWidth body arity
    let read := stoppedReaderCoefficient (pad:=pad) (s:=s) (C:=C) X body arity significant
      (initial.records.length+J6R16ModeCost.pathLimit s C)
    ∃ (A : OwnerTerminalInput X p w Y) (older : List Cmd),
      (ownerInputs p w Y stop).result=some A ∧
      (oldCompiler X p w Y A).result=some older ∧
      positiveSetup X p w Y A≤prep ∧ positiveReadBill X p w Y older B≤read*2^(6*leafH s) ∧
      (T.frame path.reached).decode L.result=
        J6R9Recursive.reduce (ch).prec f ell ((ch).host.contract X.hf) ∧
      L.steps≤(ownerInputs p w Y stop).steps+
        (prep+read+sourceArithmetic s C (ext))*2^(7*leafH s) := by
  obtain ⟨A,older,yes,compile,value,fees⟩ := actual_positive_readLeaf_with_printed_factor
    X p w M basePos ord ownerInputs gate boot initial first legal supply gateWidth stop positive
  have h := payloadWidths A yes
  have setup := true_positive_preparation_from_chart_dimensions X p w (sourceState M p w) A
    stop birthWord ownerWord h.1 h.2
  have reader := actual_stacked_ordered_leaf_reader_price X M p w gate boot gateWidth A initial first legal
    hn hs baseFit enc h.1 h.2 older compile
  exact ⟨A,older,yes,compile,setup,reader,value,
    fees.trans (structural_leaf_fee_into_printed_rate (K:=6) setup reader)⟩

#print axioms stoppedPreparationCoefficient
#print axioms positive_readLeaf_with_real_reader_and_explicit_provider
end
end J6R82LeafTime