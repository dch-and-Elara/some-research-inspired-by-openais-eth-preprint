import J6R75RawPeakLayoutPhysical
import J6R75RawPeakLayoutCandidateAttach

/-! Same physical layout entrance and entering raw carrier during
its actual finite conditional-expectation candidate/score stage. -/
namespace J6R75RawPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 J6R22Active J6R9Recursive
open J6R63Active J6R62ActivePrep J6R64Active J6R66Active J6R58ActivePrep
open J6R51Online J6R48DFS J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R16ModeCost J6R24MeteredRecursion J6R49DFS J6R49LiveBits
open J6R68ActiveInputs J6R68ActiveInputs.Sweep J6R68.RecursivePeak J6R66.BootPeak
open J6R50Peak J6R51Peak J6R52Peak J6R53PeakAddon J6R54PeakInput J6R57LiveSpace J6R57ScopeFee
open J6R72SameRunRawScope J6R68.RetireScratch J6R52FreshExterior

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4750
set_option maxHeartbeats 26500000

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)

open J6R21Ancestor J6R17ModeTape J6R12CollisionGreedyStep J6R14LayoutCost V8NativeMessage.N2DLabels
open scoped Classical

open J6R12CollisionMenu J6R12CollisionSource J6R12CollisionRun J6R12CollisionPacking
open J6R10Repack P11FullPacking

section FiniteFormat
variable {E R C' : Type*} [Fintype E] [Fintype R] [Fintype C'] {a : ℕ}
variable {N : Network E R C'}

def ActualGreedyIngressWindow
    (I : Full64Input N a) (W : Ingress I)
    (pre : List (R⊕C')) (target : R⊕C') (post : List (R⊕C'))
    (resident roof : ℕ) : Prop :=
    let F := I.format
    let start := initGraph F.kR F.kC W.paid.result.2
    let out := drive F.e F.kR F.kC F.b W.paid.result.1 start.result
    ∃ (first : Fin a→Fin 64) (rest : List (Fin a→Fin 64)),
      let menu := (menuMachine F.b)
      let seeds := literalSeed F.width F.b
      let ordered := J6R12CollisionRun.run F.width F.kR F.kC F.b F.literals (F.label first)
        (rest.map F.label)
      let previous := ordered (pre.map F.target) start.result
      let p := (J6R12CollisionRun.spec F first rest pre (fun _=>none)).1
      let choose := chooseAndWrite F.width F.kR F.kC F.b F.literals previous.result.1 (F.target target)
        (F.label first) (rest.map F.label)
      let next := ordered (post.map F.target) choose.result.1
      let score := computeCandidate F.width F.kR F.kC F.b F.literals previous.result.1 (F.target target)
      let held := resident+(rawLayoutBits rawLayoutTargetBits W.paid.result.1+
        rawLayoutBits rawIncidenceLayoutBits W.paid.result.2+rawLayoutBits rawEdgeLayoutBits start.result+
        gridMemoryBits menu.result+gridMemoryBits previous.result.2)
      let room := roof+((1+max F.kR F.kC)*I.order.length+(F.kR+F.kC)*Fintype.card E+
        (F.kR+F.kC+2)*Fintype.card E+F.b*2^F.b+F.b*pre.length)
      out=⟨(next.result.1,previous.result.2++choose.result.2::next.result.2),
        menu.steps+seeds.steps+(previous.steps+choose.steps+next.steps+2*F.b+6)+8⟩ ∧
      previous.result.1=F.graph p ∧
      ∀ label : Fin a→Fin 64,
        RealCandidateCall F.width F.b score (F.label first) (rest.map F.label) (F.label label) ∧
        ActualCandidateWorkspace F p target label held room
end FiniteFormat

variable {rank : ℕ}
local instance GREdges : Fintype c.host.Edge := c.host.finiteEdge
local instance GRRows : Fintype c.host.Row := c.host.finiteRow
local instance GRCols : Fintype c.host.Col := c.host.finiteCol

theorem same_raw_layout_candidate_scoring_keeps_the_selected_path_carrier
    {header : DirRow key}
    (D : CurrentLayoutSources T key prec tw bw page rank header)
    (M : Machine) (chart : MountedChart T) (B : L) (own : OwnsHeader header B)
    (inherit : (bank : L)→OwnsHeader header bank→Meter (CallWords r prec ew))
    (fit : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (on : (S).cutoff<x.edges),
      InputFits sel (readyAtPath T p on) q)
    (p : Path sel r c) (on : (S).cutoff<c.edges) (shared carry roof : ℕ)
    (bound : recursiveResidentBits shared M B p carry+
      exactAncestorJetWidth M (D.retained fit) chart (D.rootInputs inherit) B own p≤roof)
    (pre : List (c.host.Row⊕c.host.Col)) (target : c.host.Row⊕c.host.Col) (post : List (c.host.Row⊕c.host.Col))
    (split : (D.atPath M B own p on).input.order=pre++target::post) :
    let F := D.retained fit
    let E := D.rootInputs inherit
    let input := literalStockCapturesAt M F E B own p on
    let words := input.2.1.result
    let W := D.atPath M B own p on
    let resident := recursiveResidentBits shared M B p carry+exactAncestorJetWidth M F chart E B own p
    let held := resident+(words.precision.bits.length+words.edges.bits.length+gridMemoryBits chart.table.raw)
    let room := roof+(prec+input.1+f.natDegree*chart.count)
    input.2.2=W.run ∧
    ActualGreedyIngressWindow W.input W.bytes pre target post held room := by
  let F := D.retained fit
  let E := D.rootInputs inherit
  let input := literalStockCapturesAt M F E B own p on
  let words := input.2.1.result
  let W := D.atPath M B own p on
  have exactHeaders :
      words.precision.bits.length+words.edges.bits.length+gridMemoryBits chart.table.raw=
        prec+input.1+f.natDegree*chart.count := by
    rw [words.precision.size,words.edges.size,
      uniform_grid_bits f.natDegree chart.table.raw chart.table.width,chart.table.length]
  refine ⟨chosen_layout_path_uses_the_real_root_or_descendant_producer D M B own inherit fit p on,?_⟩
  exact actual_greedy_layout_candidate_after_real_target_prefix_has_pair_space W.input W.bytes
    pre target post split _ _ (Nat.add_le_add bound exactHeaders.le)

#print axioms same_raw_layout_candidate_scoring_keeps_the_selected_path_carrier
end
end J6R75RawPeak
