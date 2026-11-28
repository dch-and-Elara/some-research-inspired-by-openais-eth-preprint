import J6R62LeafFreshFormat
import J6R57PublicNoChartOnline
import J6R51OnlineFeeDefs

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 45000000
set_option maxRecDepth 5400

/-! The finite charge goes into the existing actual R51/R56 `readLeaf`
interface. Positive installed leaves no longer need a bound on that
entire callback. Producer and ancestral packet formats remain explicit. -/
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
local notation "Bank" => PageBank f ell key prec tw bw (pageKeyWidth m+pad)
local notation "Cmd" => ReadCmd key (pageKeyWidth m+pad)

theorem successful_terminal_has_true_old_compiler_list
    (Y : StoredSite T (p.ticket w) key prec tw bw (pageKeyWidth m+pad))
    (input : Meter (OwnerTerminalInput X p w Y))
    (F : J6R24MeteredRecursion.Frame f (p.ticket w).child.prec)
    (B : Bank) (ans : Block F ell)
    (on : (executeOwnerTerminal X p w Y input F B).result=some ans) :
    ∃ older : List Cmd,(oldCompiler X p w Y input.result).result=some older := by
  change (joinPaidTerminal Y input.result.saved (oldCompiler X p w Y input.result) F B).result=some ans at on
  cases hex : (oldCompiler X p w Y input.result).result with
  | none =>
    simp only [joinPaidTerminal,hex] at on
    contradiction
  | some older => exact ⟨older,rfl⟩

variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (basePos : 0<base)
variable (ord : Fin ((exteriorChild G ell X.centre X.sample X.group)).edges≃((exteriorChild G ell X.centre X.sample X.group)).host.Edge)
variable (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)

theorem read_leaf_uses_positive_owner_runtime
    (initial : Bank) (stop : ((Plan sel).child c w).edges≤(printedParams (f:=f) (ell:=ell) s).cutoff)
    (positive : 0<((Plan sel).child c w).edges) :
    let Y := sourceState M p w
    let B := stackBank (borns M) initial (Path.step p w)
    readLeaf (withPaidOwnerLeaves X M basePos ord ownerInputs) initial (Path.step p w) stop=
      runOwnerPositive (X:=X) (ownerInputs:=ownerInputs) (p:=p) (w:=w) (Y:=Y) (stop:=stop) (B:=B) := by
  let R := withPaidOwnerLeaves X M basePos ord ownerInputs
  let walk := Path.step p w
  let B := stackBank (borns M) initial walk
  have bankEq : stackBank (borns R) initial walk=B :=
    congrArg (fun BB : Births T key prec tw bw (pageKeyWidth m+pad)=>stackBank BB initial walk)
      (paid_owner_leaf_keeps_births X M basePos ord ownerInputs)
  change R.leafAfter p w (sourceState R p w) stop (stackBank (borns R) initial walk)=_
  rw [bankEq,paid_owner_leaf_keeps_actual_source X M basePos ord ownerInputs p w]
  simp only [R,withPaidOwnerLeaves,if_neg (Nat.ne_of_gt positive),B,walk]

variable (gate : Stamp key prec)
variable (boot : ExactPrintedBoot X M gate)

include boot in
theorem actual_positive_leaf_value_and_canonical_fee
    (initial : Bank) (stop : ((Plan sel).child c w).edges≤(printedParams (f:=f) (ell:=ell) s).cutoff)
    (positive : 0<((Plan sel).child c w).edges) (gateWidth : gate.created.val=base)
    (rootLive : IsLive (X.seed pad) initial) (valid : ReadyOnStack (borns M) initial)
    (supplier : HasMeasuredOwnerInputs X M ownerInputs)
    (oldFormat :
      let Y := sourceState M p w
      let B := stackBank (borns M) initial (Path.step p w)
      ∀ (A : OwnerTerminalInput X p w Y) (older : List Cmd),
        (ownerInputs p w Y stop).result=some A →
        (oldCompiler X p w Y A).result=some older →
        ∀ cmd∈older,ReadFormat B (p.ticket w).child.edges cmd) :
    let Y := sourceState M p w
    let walk := Path.step p w
    let F := T.frame walk.reached
    let B := stackBank (borns M) initial walk
    let leaf := readLeaf (withPaidOwnerLeaves X M basePos ord ownerInputs) initial walk stop
    ∃ (A : OwnerTerminalInput X p w Y) (older : List Cmd),
      (ownerInputs p w Y stop).result=some A ∧
        (oldCompiler X p w Y A).result=some older ∧
        F.decode leaf.result=reduce (p.ticket w).child.prec f ell ((p.ticket w).child.host.contract X.hf) ∧
        leaf.steps≤canonicalLeafFee X p w Y ⟨A,(ownerInputs p w Y stop).steps⟩ F B older+3 := by
  let Y := sourceState M p w
  let walk := Path.step p w
  let F := T.frame walk.reached
  let B := stackBank (borns M) initial walk
  have live : opened (borns M) (IsLive (X.seed pad)) walk B :=
    stack_is_opened (borns M) initial (IsLive (X.seed pad)) (live_monotone (X.seed pad))
      rootLive valid walk
  have measured := supplier p w stop positive
  change (ownerInputs p w Y stop).result.isSome at measured
  cases which : (ownerInputs p w Y stop).result with
  | none => simp only [which,Option.isSome_none,Bool.false_eq_true] at measured
  | some A =>
    let input : Meter (OwnerTerminalInput X p w Y) := ⟨A,(ownerInputs p w Y stop).steps⟩
    have rootHere := opened_keeps_root X pad (borns M) walk B live
    obtain ⟨word,read,decode⟩ :=
      actual_owner_terminal_correct_without_legacy_chart X M gate boot p w input F B
        gateWidth basePos positive (IsLive (X.seed pad)) rootHere live
    obtain ⟨older,compiled⟩ := successful_terminal_has_true_old_compiler_list X p w Y input F B word read
    have born : OnPath (borns M) Y.birth.job walk := .youngest p w rfl
    have form (cmd : Cmd) (belongs : cmd∈older++(trueFreshPages Y).map (freshWord Y)) :
        ReadFormat B (p.ticket w).child.edges cmd := by
      rcases List.mem_append.mp belongs with h|h
      · exact oldFormat A older which compiled cmd h
      · exact actual_compiled_atlas_read_formats Y walk (borns M) born (IsLive (X.seed pad))
          B live (p.ticket w).child.edges cmd h
    have fee := exact_owner_terminal_finite_fee X p w Y input F B older compiled form
    refine ⟨A,older,which,compiled,?_⟩
    dsimp only
    rw [read_leaf_uses_positive_owner_runtime X p w M basePos ord ownerInputs initial stop positive,
      accepted_owner_inputs_use_the_actual_reader X ownerInputs p w Y stop B A which word read]
    exact ⟨decode,Nat.add_le_add_right fee _⟩

#print axioms successful_terminal_has_true_old_compiler_list
#print axioms read_leaf_uses_positive_owner_runtime
#print axioms actual_positive_leaf_value_and_canonical_fee
end
end J6R62Leaf
