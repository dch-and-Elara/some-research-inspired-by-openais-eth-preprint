import J6R94HeldOwnerProviderCap

/-! The R65 stopped-positive interpreter executed with the concrete held owner producer, on the original live stack. The whole-meter identity with a selected legacy callback is kept distinct from this implementation. -/
namespace J6R94HeldOwnerProvider
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R50Leaf J6R50SourceProducer J6R51Leaf J6R51Online J6R49Leaf J6R48Leaf
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

open J6R52CacheWhole J6R82LeafTime J6R9Recursive J6R58LeafScale J6R21Leaf

def readProvidedOnR65Bank
    (input : Meter (OwnerTerminalInput X p w (sourceState M p w))) (initial : Bank) :
    Meter (Block (T.frame (Path.step p w).reached) ell) :=
  let F := T.frame (Path.step p w).reached
  let B := stackBank (borns M) initial (.step p w)
  finishOwnerAttempt F (executeOwnerTerminal X p w (sourceState M p w) input F B)

section Legacy
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel)
  (exteriorChild G ell X.centre X.sample X.group))]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (basePos : 0<base)
variable (ord : Fin (exteriorChild G ell X.centre X.sample X.group).edges ≃
  (exteriorChild G ell X.centre X.sample X.group).host.Edge)
variable (ownerInputs : OwnerInputProvider (T:=T) (pad:=pad) X)

/-- The old ABI has no resident owner state. If one *actually* installs
    the specified direct input acquisition at this call, the old
    stopped run equals the same complete meter, not just the answer. -/
theorem r65_positive_is_the_selected_actual_provider
    (initial : Bank) (input : Meter (OwnerTerminalInput X p w (sourceState M p w)))
    (stop : ((Plan sel).child c w).edges≤(printedParams (f:=f) (ell:=ell) s).cutoff)
    (positive : 0<((Plan sel).child c w).edges)
    (receipt : ownerInputs p w (sourceState M p w) stop=⟨some input.result,input.steps⟩) :
    readLeaf (withPaidOwnerLeaves X M basePos ord ownerInputs) initial (.step p w) stop=
      readProvidedOnR65Bank X M p w input initial := by
  rw [read_leaf_uses_positive_owner_runtime X p w M basePos ord ownerInputs initial stop positive]
  unfold runOwnerPositive readProvidedOnR65Bank
  dsimp only
  rw [receipt]
end Legacy

variable (gate : Stamp key prec) (boot : ExactPrintedBoot X M gate)
variable (gateWidth : gate.created.val=base) (hBase : 0<base)

include boot gateWidth hBase in
theorem provided_source_leaf_value_and_true_finite_cost
    (initial : Bank) (live : IsLive (X.seed pad) initial) (legal : ReadyOnStack (borns M) initial)
    (input : Meter (OwnerTerminalInput X p w (sourceState M p w)))
    (stop : ((Plan sel).child c w).edges≤(printedParams (f:=f) (ell:=ell) s).cutoff)
    (positive : 0<((Plan sel).child c w).edges) :
    let Y := sourceState M p w
    let path := Path.step p w
    let B := stackBank (borns M) initial path
    let F := T.frame path.reached
    let L := readProvidedOnR65Bank X M p w input initial
    ∃ older : List Cmd,
      (oldCompiler X p w Y input.result).result=some older ∧
      F.decode L.result=reduce (ch).prec f ell ((ch).host.contract X.hf) ∧
      L.steps≤finiteStopFee input.steps (positiveSetup X p w Y input.result)
        (positiveReadBill X p w Y older B) (sourceArithmetic s C (ext)) (leafH s) := by
  let Y := sourceState M p w
  let path := Path.step p w
  let B := stackBank (borns M) initial path
  let F := T.frame path.reached
  let L := readProvidedOnR65Bank X M p w input initial
  have openedNow : opened (borns M) (IsLive (X.seed pad)) path B :=
    stack_is_opened (borns M) initial (IsLive (X.seed pad)) (live_monotone (X.seed pad)) live legal path
  have outside := opened_keeps_root X pad (borns M) path B openedNow
  obtain ⟨word,read,decode⟩ := actual_owner_terminal_correct_without_legacy_chart X M gate boot
    p w input F B gateWidth hBase positive (IsLive (X.seed pad)) outside openedNow
  obtain ⟨older,compiled⟩ := successful_terminal_has_true_old_compiler_list X p w Y input F B word read
  have current : OnPath (borns M) Y.birth.job path := .youngest p w rfl
  have forms (cmd : Cmd) (member : cmd∈older++(trueFreshPages Y).map (freshWord Y)) :
      ReadFormat B (ch).edges cmd := by
    rcases List.mem_append.mp member with left|right
    · exact every_actual_retained_owner_command_is_formatted X M p w gate boot gateWidth input.result
        (IsLive (X.seed pad)) B outside openedNow older compiled cmd left
    · exact actual_compiled_atlas_read_formats Y path (borns M) current (IsLive (X.seed pad))
        B openedNow (ch).edges cmd right
  let U := observedFrameWidth input.result.saved.rows
  let d := observedGateWidth input.result.roster.raw
  have fee := actual_terminal_with_source_sizes X p w Y input B older compiled forms U d
    (frame_width_is_observed input.result.saved.rows) (gate_width_is_observed input.result.roster.raw)
  have exactResult : L=⟨word,(executeOwnerTerminal X p w Y input F B).steps+3⟩ := by
    unfold L readProvidedOnR65Bank finishOwnerAttempt
    dsimp only
    rw [read]
  refine ⟨older,compiled,?_⟩
  change F.decode L.result=_ ∧ L.steps≤_
  rw [exactResult]
  refine ⟨decode,?_⟩
  have ds := actual_leaf_field_width_and_vertices (T:=T) path
  let bill := positiveReadBill X p w Y older B
  let raw := rawLeafCap (4*Nat.clog 2 s) ell (ch).prec (ch).edges (vertexCount (ch).host) bill F.hp
  have rawPrice : raw≤2^(leafH s)*(bill+sourceArithmetic s C (ext)) :=
    raw_leaf_fee_from_dimensions F.hp le_rfl le_rfl ds.2.1 stop ds.2.2
  have singleBound : L.steps ≤ input.steps+positiveSetup X p w Y input.result+raw := by
    rw [exactResult]
    have total := Nat.add_le_add_right fee 3
    change (executeOwnerTerminal X p w Y input F B).steps+3≤_ at total
    unfold sizedCanonicalLeafFee at total
    change (executeOwnerTerminal X p w Y input F B).steps+3≤
      input.steps+ownerCensusFee X p w Y U d+atlasCensusFee X p w Y U+
      (4*Nat.card (ch).host.Row+3)+(4*(ch).edges+2)+raw+15+3 at total
    unfold positiveSetup
    dsimp only
    have u : observedFrameWidth input.result.saved.rows=U := rfl
    have v : observedGateWidth input.result.roster.raw=d := rfl
    rw [u,v]
    omega
  exact (show L.steps≤finiteStopFee input.steps (positiveSetup X p w Y input.result) bill
      (sourceArithmetic s C (ext)) (leafH s) from singleBound.trans (Nat.add_le_add_left rawPrice _))
    |> fun h=>by rw [exactResult] at h; exact h

#print axioms r65_positive_is_the_selected_actual_provider
#print axioms provided_source_leaf_value_and_true_finite_cost
end
end J6R94HeldOwnerProvider