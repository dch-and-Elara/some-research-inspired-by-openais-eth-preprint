import J6R62LeafPositiveLedger
import J6R62LeafOldFormat
import J6R62LeafSized

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 47000000
set_option maxRecDepth 5600

/-! Derive the positive installed leaf charge from exact source inputs,
including both kinds of retained page and the current fresh atlas. The
measured input producer is deliberately not assumed free. -/
namespace J6R62Leaf
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6R27OriginalGate J6OrientedHost
open J6Mesh J6R35RootOrigins J6R37StructuredRoot J6R34RootAtlas J6R31RootResidentTables
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R32RootGeneratedRegistryInputs
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R50SourceProducer
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R22Active J6R24MeteredRecursion
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R49SourceLayout
open J6R51ParentFrames J6R51Online J6R52Terminal J6R53TerminalGate J6R53TerminalExterior
open J6R53OldOwner J6R50Leaf J6R41StructuredAllPaths J6R54TerminalBoot J6R51Leaf J6R48DFS
open J6R48Leaf J6R57Public

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
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (basePos : 0<base)
variable (ord : Fin ((exteriorChild G ell X.centre X.sample X.group)).edges≃((exteriorChild G ell X.centre X.sample X.group)).host.Edge)
variable (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)
variable (gate : Stamp key prec)
variable (boot : ExactPrintedBoot X M gate)

include boot in
theorem mounted_positive_leaf_is_exact_and_has_source_sized_fee
    (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
    (stop : ((Plan sel).child c w).edges≤(printedParams (f:=f) (ell:=ell) s).cutoff)
    (positive : 0<((Plan sel).child c w).edges) (gateWidth : gate.created.val=base)
    (rootLive : IsLive (X.seed pad) initial) (valid : ReadyOnStack (borns M) initial)
    (supplier : HasMeasuredOwnerInputs X M ownerInputs) :
    let Y := sourceState M p w
    let walk := Path.step p w
    let F := T.frame walk.reached
    let B := stackBank (borns M) initial walk
    let leaf := readLeaf (withPaidOwnerLeaves X M basePos ord ownerInputs) initial walk stop
    ∃ (A : OwnerTerminalInput X p w Y) (older : List (ReadCmd key (pageKeyWidth m+pad))),
      (ownerInputs p w Y stop).result=some A ∧
        (oldCompiler X p w Y A).result=some older ∧
        F.decode leaf.result=reduce (p.ticket w).child.prec f ell ((p.ticket w).child.host.contract X.hf) ∧
        leaf.steps≤sizedCanonicalLeafFee X p w Y ⟨A,(ownerInputs p w Y stop).steps⟩ B older
          (observedFrameWidth A.saved.rows) (observedGateWidth A.roster.raw)+3 := by
  let walk := Path.step p w
  let B := stackBank (borns M) initial walk
  let Y := sourceState M p w
  have live : opened (borns M) (IsLive (X.seed pad)) walk B :=
    stack_is_opened (borns M) initial (IsLive (X.seed pad)) (live_monotone (X.seed pad))
      rootLive valid walk
  have rootHere := opened_keeps_root X pad (borns M) walk B live
  have measured := actual_positive_leaf_value_and_canonical_fee X p w M basePos ord ownerInputs
    gate boot initial stop positive gateWidth rootLive valid supplier
    (fun A older _ compiled cmd used=>every_actual_retained_owner_command_is_formatted
      X M p w gate boot gateWidth A (IsLive (X.seed pad)) B rootHere live older compiled cmd used)
  obtain ⟨A,older,supplied,compiled,decode,fee⟩ := measured
  have cap := actual_terminal_cap_has_source_sizes X p w Y ⟨A,(ownerInputs p w Y stop).steps⟩
    B older compiled (observedFrameWidth A.saved.rows) (observedGateWidth A.roster.raw)
    (frame_width_is_observed A.saved.rows) (gate_width_is_observed A.roster.raw)
  exact ⟨A,older,supplied,compiled,decode,fee.trans (Nat.add_le_add_right cap 3)⟩

#print axioms mounted_positive_leaf_is_exact_and_has_source_sized_fee
end
end J6R62Leaf
