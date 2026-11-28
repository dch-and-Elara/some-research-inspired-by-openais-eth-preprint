import J6R110CanonicalAllPeakBoot
import J6R110CanonicalCoveragePath
import J6R75RawPeakMaxPausePair

/-! The active phases that already name the raw probe table use the
bare shared carrier. Their concrete comparison with a table boot
cut does not introduce a second copy of the resident table. -/
namespace J6R110CanonicalAllPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 J6R22Active J6R9Recursive
open J6R63Active J6R62ActivePrep J6R64Active J6R66Active J6R58ActivePrep
open J6R51Online J6R48DFS J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R16ModeCost J6R24MeteredRecursion J6R49DFS J6R49LiveBits
open J6R68ActiveInputs J6R68ActiveInputs.Sweep J6R68.RecursivePeak J6R66.BootPeak
open J6R50Peak J6R51Peak J6R52Peak J6R53PeakAddon J6R54PeakInput J6R57LiveSpace J6R57ScopeFee
open J6R72SameRunRawScope J6R68.RetireScratch J6R52FreshExterior
open J6R75RawPeak J6R110CanonicalCoverage J6R110CanonicalMount J6R109CanonicalProbeTable
open J6R21Ancestor J6R17ModeTape J6R12CollisionGreedyStep J6R14LayoutCost V8NativeMessage.N2DLabels

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option quotPrecheck false
set_option maxHeartbeats 23000000
set_option maxRecDepth 4800

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q ew rank : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)
local notation "e" => f.natDegree
local notation "d" => (fullProbeDegree f.natDegree)
local notation "n" => (fullProbeDegree f.natDegree+1)
local notation "Fcap" => (full_probe_fit f.natDegree)
local instance activePeakEdges : Fintype c.host.Edge := c.host.finiteEdge
local instance activePeakRows : Fintype c.host.Row := c.host.finiteRow
local instance activePeakCols : Fintype c.host.Col := c.host.finiteCol

def CanonicalActiveCutMaxima
    {header : DirRow key}
    (D : CurrentLayoutSources T key prec tw bw page rank header)
    (M : Machine) (B : L) (own : OwnsHeader header B)
    (inherit : (bank : L)→OwnsHeader header bank→Meter (CallWords r prec ew))
    (fit : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (on : (S).cutoff<x.edges),
      InputFits sel (readyAtPath T p on) q)
    (bytes : (canonicalTable e n).result=OldOrderedBytes e d Fcap)
    (p : Path sel r c) (on : (S).cutoff<c.edges) (shared carry roof : ℕ) : Prop :=
  let F := D.retained fit
  let E := D.rootInputs inherit
  let chart := (mountFullChart T bytes).result
  let ambient := shared+mountedSelectedBits B
  let input := literalStockCapturesAt M F E B own p on
  let words := input.2.1.result
  let W := D.atPath M B own p on
  let resident := recursiveResidentBits shared M B p carry+exactAncestorJetWidth M F chart E B own p
  let held := resident+(words.precision.bits.length+words.edges.bits.length+gridMemoryBits chart.table.raw)
  let room := roof+(prec+input.1+e*chart.count)
  let scheduler := (rawScheduleAt M F chart E B own p on).result
  input.2.2=W.run ∧
  (∀ (pre : List (c.host.Row⊕c.host.Col)) (target : c.host.Row⊕c.host.Col) (post : List (c.host.Row⊕c.host.Col)),
    W.input.order=pre++target::post →
    ∀ built,CanonicalBootCut T bytes built →
      GreedyWindowAtOldMaximum W.input W.bytes pre target post held room (ambient+built) (ambient+264*s^5)) ∧
  (∀ (x : scheduler.EmitRow) (z : Probe S c) (pre : List (List Bool)) (row : List Bool) (post : List (List Bool)),
    chart.table.raw=pre++row::post → pre.length=z.val →
    let mask := (scheduler.fetch x).masks z
    let copy := copyBits row
    let seen := (pre.map copyBits).foldr resumeMaskScan ⟨some copy.result,copy.steps+4⟩
    let payload := resident+rawStockBits scheduler.stock+
      (gridMemoryBits chart.table.raw+gridMemoryBits (pre.map (fun w=>(copyBits w).result))+copy.result.length)
    (⟨mask.result.val,mask.steps⟩ : Meter (List Bool))=⟨copy.result,seen.steps⟩ ∧
    mask.steps≤464*s^5 ∧
    ∀ built,CanonicalBootCut T bytes built →
      max (ambient+built) payload≤max (ambient+264*s^5) (roof+rawStockBits scheduler.stock+256*s^5))

theorem actual_input_layout_and_scan_do_not_duplicate_the_paid_chart
    {header : DirRow key}
    (D : CurrentLayoutSources T key prec tw bw page rank header)
    (M : Machine) (B : L) (own : OwnsHeader header B)
    (inherit : (bank : L)→OwnsHeader header bank→Meter (CallWords r prec ew))
    (fit : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (on : (S).cutoff<x.edges),
      InputFits sel (readyAtPath T p on) q)
    (bytes : (canonicalTable e n).result=OldOrderedBytes e d Fcap)
    (p : Path sel r c) (on : (S).cutoff<c.edges) (shared carry roof : ℕ)
    (within : recursiveResidentBits shared M B p carry+
      exactAncestorJetWidth M (D.retained fit) (mountFullChart T bytes).result (D.rootInputs inherit) B own p≤roof)
    (controlled : ControlledLayoutPathPause D M (mountFullChart T bytes).result B own inherit fit p on
      shared carry roof) :
    CanonicalActiveCutMaxima D M B own inherit fit bytes p on shared carry roof := by
  obtain ⟨used,layout⟩ := controlled
  refine ⟨used,?_,?_⟩
  · intro pre target post cut built boot
    exact actual_controlled_layout_combines_with_the_given_bounded_cut (layout pre target post cut).2
      (Nat.add_le_add_left (actual_canonical_boot_cut_fits T bytes built boot) _)
  · intro x z pre row post split index
    obtain ⟨same,fee,space⟩ := exact_raw_path_reads_the_paid_full_table_in_its_existing_stock_room
      M (D.retained fit) bytes (D.rootInputs inherit) B own p on shared carry roof within
      x z pre row post split index
    exact ⟨same,fee,fun built boot=>same_entry_boot_and_regional_pause_take_maximum
      T bytes (shared+mountedSelectedBits B) built _ _ boot space⟩

#print axioms actual_input_layout_and_scan_do_not_duplicate_the_paid_chart
end
end J6R110CanonicalAllPeak
