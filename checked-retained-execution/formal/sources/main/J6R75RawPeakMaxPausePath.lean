import J6R75RawPeakMaxPauseIngress

/-! The controlled scorer is the scorer of the exact layout Meter
used by the real raw root or entered-child preparation. The
header and immutable mounted mask words are still present. -/
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
open J6R21Ancestor J6R17ModeTape J6R12CollisionGreedyStep J6R14LayoutCost V8NativeMessage.N2DLabels

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4850
set_option maxHeartbeats 27000000

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q ew rank : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)
local instance controlledPathEdges : Fintype c.host.Edge := c.host.finiteEdge
local instance controlledPathRows : Fintype c.host.Row := c.host.finiteRow
local instance controlledPathCols : Fintype c.host.Col := c.host.finiteCol

def ControlledLayoutPathPause
    {header : DirRow key}
    (D : CurrentLayoutSources T key prec tw bw page rank header)
    (M : Machine) (chart : MountedChart T) (B : L) (own : OwnsHeader header B)
    (inherit : (bank : L)→OwnsHeader header bank→Meter (CallWords r prec ew))
    (fit : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (on : (S).cutoff<x.edges),
      InputFits sel (readyAtPath T p on) q)
    (p : Path sel r c) (on : (S).cutoff<c.edges) (shared carry roof : ℕ) : Prop :=
    let F := D.retained fit
    let E := D.rootInputs inherit
    let input := literalStockCapturesAt M F E B own p on
    let words := input.2.1.result
    let W := D.atPath M B own p on
    let resident := recursiveResidentBits shared M B p carry+exactAncestorJetWidth M F chart E B own p
    let held := resident+(words.precision.bits.length+words.edges.bits.length+gridMemoryBits chart.table.raw)
    let room := roof+(prec+input.1+f.natDegree*chart.count)
    input.2.2=W.run ∧
    ∀ (pre : List (c.host.Row⊕c.host.Col)) (target : c.host.Row⊕c.host.Col) (post : List (c.host.Row⊕c.host.Col)),
      W.input.order=pre++target::post →
        ActualGreedyIngressWindow W.input W.bytes pre target post held room ∧
        ControlledGreedyIngressWindow W.input W.bytes pre target post held room

theorem actual_selected_path_observes_its_controlled_original_greedy_pause
    {header : DirRow key}
    (D : CurrentLayoutSources T key prec tw bw page rank header)
    (M : Machine) (chart : MountedChart T) (B : L) (own : OwnsHeader header B)
    (inherit : (bank : L)→OwnsHeader header bank→Meter (CallWords r prec ew))
    (fit : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (on : (S).cutoff<x.edges),
      InputFits sel (readyAtPath T p on) q)
    (p : Path sel r c) (on : (S).cutoff<c.edges) (shared carry roof : ℕ)
    (bound : recursiveResidentBits shared M B p carry+
      exactAncestorJetWidth M (D.retained fit) chart (D.rootInputs inherit) B own p≤roof) :
    ControlledLayoutPathPause D M chart B own inherit fit p on shared carry roof := by
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
  intro pre target post split
  have old := (same_raw_layout_candidate_scoring_keeps_the_selected_path_carrier D M chart B own
    inherit fit p on shared carry roof bound pre target post split).2
  exact ⟨old,actual_greedy_layout_reuses_one_controlled_candidate_pause W.input W.bytes
    pre target post split _ _ (Nat.add_le_add bound exactHeaders.le)⟩

#print axioms actual_selected_path_observes_its_controlled_original_greedy_pause
end
end J6R75RawPeak
