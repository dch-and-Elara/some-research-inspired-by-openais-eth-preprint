import J6R75RawPeakStockAttach
import J6R75RawPeakLayoutJob
import J6R68ActiveInputsSweepPhysical

/-! Same actual chosen exterior/after layout consumed by the raw
runner, using the current literal stock capture and its ancestor
payload, not a clone with merely the same completed count. -/
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

private theorem transported_layout_keeps_its_actual_byte_fields
    {a b q i j : ℕ} (e : i=j) (out : Meter (LayoutReceipt a b q i)) :
    (transportLayout e out).result.boxes=out.result.boxes ∧
    (transportLayout e out).result.copies.bits=out.result.copies.bits := by
  subst j
  exact ⟨rfl,rfl⟩

noncomputable section
variable {rank : ℕ}
local instance liveEdgeType : Fintype c.host.Edge := c.host.finiteEdge
local instance liveRowType : Fintype c.host.Row := c.host.finiteRow
local instance liveColType : Fintype c.host.Col := c.host.finiteCol

theorem current_chosen_layout_keeps_the_real_greedy_return_at_same_bytes
    {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c}
    (W : ChosenSetup sel d rank) :
    let layout := runWithIngress W.input rank W.bytes
    W.run.result.boxes=layout.result.boxes ∧
    W.run.result.copies.bits=layout.result.copies := by
  unfold ChosenSetup.run
  dsimp only
  exact transported_layout_keeps_its_actual_byte_fields _ _

theorem chosen_layout_path_uses_the_real_root_or_descendant_producer
    {header : DirRow key}
    (D : CurrentLayoutSources T key prec tw bw page rank header)
    (M : Machine) (B : L) (own : OwnsHeader header B)
    (inherit : (bank : L)→OwnsHeader header bank→Meter (CallWords r prec ew))
    (fit : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (on : (S).cutoff<x.edges),
      InputFits sel (readyAtPath T p on) q)
    (p : Path sel r c) (on : (S).cutoff<c.edges) :
    (literalStockCapturesAt M (D.retained fit) (D.rootInputs inherit) B own p on).2.2=
      (D.atPath M B own p on).run := by
  cases p <;> rfl

/-- The layout scratch is attached to an actual root or entered active
child. Its common input is the existing selected path payload, actual
decoded header, and the mounted immutable masks. The current stock
producing phase is distinct; its retained ancestor words are the same.
The supplied ingress/raw chart builders still have no inferred peak. -/
theorem actual_raw_path_layout_uses_one_original_physical_workspace
    {header : DirRow key}
    (D : CurrentLayoutSources T key prec tw bw page rank header)
    (M : Machine) (chart : MountedChart T) (B : L) (own : OwnsHeader header B)
    (inherit : (bank : L)→OwnsHeader header bank→Meter (CallWords r prec ew))
    (fit : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (on : (S).cutoff<x.edges),
      InputFits sel (readyAtPath T p on) q)
    (p : Path sel r c) (on : (S).cutoff<c.edges) (shared carry roof : ℕ)
    (bound : recursiveResidentBits shared M B p carry+
      exactAncestorJetWidth M (D.retained fit) chart (D.rootInputs inherit) B own p≤roof) :
    let F := D.retained fit
    let E := D.rootInputs inherit
    let input := literalStockCapturesAt M F E B own p on
    let words := input.2.1.result
    let used := input.2.2
    let W := D.atPath M B own p on
    let actual := runWithIngress W.input rank W.bytes
    let d := readyAtPath T p on
    let resident := recursiveResidentBits shared M B p carry+exactAncestorJetWidth M F chart E B own p
    let held := resident+(words.precision.bits.length+words.edges.bits.length+gridMemoryBits chart.table.raw)
    let room := roof+(prec+input.1+f.natDegree*chart.count)
    used=W.run ∧
    used.result.boxes=actual.result.boxes ∧
    used.result.copies.bits=actual.result.copies ∧
    LiteralRawLayoutPhases W.input W.bytes rank (wordsOf (packing sel d)) held room := by
  let F := D.retained fit
  let E := D.rootInputs inherit
  let input := literalStockCapturesAt M F E B own p on
  let words := input.2.1.result
  let W := D.atPath M B own p on
  let d := readyAtPath T p on
  let resident := recursiveResidentBits shared M B p carry+exactAncestorJetWidth M F chart E B own p
  let room := roof+(prec+input.1+f.natDegree*chart.count)
  have source := chosen_layout_path_uses_the_real_root_or_descendant_producer D M B own inherit fit p on
  obtain ⟨boxes,copies⟩ := current_chosen_layout_keeps_the_real_greedy_return_at_same_bytes W
  have captured :
      words.precision.bits.length+words.edges.bits.length+gridMemoryBits chart.table.raw=
        prec+input.1+f.natDegree*chart.count := by
    rw [words.precision.size,words.edges.size,
      uniform_grid_bits f.natDegree chart.table.raw chart.table.width,chart.table.length]
  refine ⟨source,?_,?_,?_⟩
  · change input.2.2.result.boxes=(runWithIngress W.input rank W.bytes).result.boxes
    rw [show input.2.2=W.run from source]
    exact boxes
  · change input.2.2.result.copies.bits=(runWithIngress W.input rank W.bytes).result.copies
    rw [show input.2.2=W.run from source]
    exact copies
  have legal : Fintype.card c.host.Edge<2^rank :=
    (layout_actual_edge_count d).symm ▸ W.fit
  have roomFit : resident+(words.precision.bits.length+words.edges.bits.length+
      gridMemoryBits chart.table.raw)≤room :=
    Nat.add_le_add bound captured.le
  exact true_greedy_layout_groups_and_exports_with_its_named_ingress_live W.input W.bytes
    rank W.pos W.dim legal W.coordinate (wordsOf (packing sel d)) W.exactLabels _ _ roomFit

#print axioms current_chosen_layout_keeps_the_real_greedy_return_at_same_bytes
#print axioms chosen_layout_path_uses_the_real_root_or_descendant_producer
#print axioms actual_raw_path_layout_uses_one_original_physical_workspace
end
end
end J6R75RawPeak
