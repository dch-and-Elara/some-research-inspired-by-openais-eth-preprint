import J6R82LeafTimeOrdered
import J6R82LeafTimeEncoding

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

variable (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate)
variable (gateWidth : gate.created.val=base)
variable (A : OwnerTerminalInput X p w (sourceState M p w))

include boot gateWidth in
theorem actual_singleton_mount_reader_has_computed_width_and_record_cap
    (legal : ReadyOnStack (borns M) (mountFromEmpty (X.seed pad)).result.1)
    (hn : native≤m) (hs : s=physicalSize m native) (baseFit : base≤C*s)
    {body arity : ℕ}
    (frameFit : observedFrameWidth A.saved.rows≤body)
    (gateFit : observedGateWidth A.roster.raw≤arity)
    (older : List Cmd) (compiled : (oldCompiler X p w (sourceState M p w) A).result=some older) :
    let B := (mountFromEmpty (X.seed pad)).result.1
    let significant := realLookupWidth q (pageKeyWidth m+pad) bw
    positiveReadBill X p w (sourceState M p w) older (stackBank (borns M) B (.step p w))≤
      stoppedReaderCoefficient (pad:=pad) (s:=s) (C:=C) X body arity significant
        (1+J6R16ModeCost.pathLimit s C)*2^(6*leafH s) := by
  let B := (mountFromEmpty (X.seed pad)).result.1
  have mount := actual_empty_mount (X.seed pad)
  have rr := actual_stacked_ordered_leaf_reader_price X M p w gate boot gateWidth A B mount.2.1
    legal hn hs baseFit (real_stack_encoding_from_singleton_mount X M (.step p w))
    frameFit gateFit older compiled
  have one : B.records.length=1 := mount.2.2.2
  rw [one] at rr
  exact rr

#print axioms actual_singleton_mount_reader_has_computed_width_and_record_cap
end
end J6R82LeafTime