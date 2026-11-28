
import J6R51PeakOnlineBodies
import J6R51PeakStack

/-! Bind the descriptor budget to the same demand-produced source
state, not an independently supplied family of future descriptors.
The actual root's serialized body width and selected scalar word
widths are still parameters of this model. -/
namespace J6R51Peak
open scoped Polynomial
open AOracleMachineTime J6R21Ancestor J1PPrinted J6ActiveRun J6R10Reachable
open J6R11Blueprint J6R12Blueprint J6R16ModeCost
open J6R10Repack J6R24MeteredRecursion J6R26DescriptorTree J6R34ChildPath
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS J6R50SourceProducer J6R51Online

set_option autoImplicit false
set_option maxHeartbeats 16500000
set_option maxRecDepth 3500

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page
local notation "P" => (Plan sel)

def EntryWidths (M : OnlineMachine T key prec tw bw page q) (fixed addr : ℕ) : Prop :=
  ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (P).Slot x),
    fixedWords (borns M p w)≤fixed ∧ (borns M p w).port+6≤addr

def BootBodyWidth (M : OnlineMachine T key prec tw bw page q) (seed : ℕ) : Prop :=
  ∀ (w : (P).Slot r) (h : Port r.host.Edge),
    ((M.initial w).result.birth.native.physical.record h).body.length≤seed

theorem geometry_of_real_demand_caps_the_raw_header (M : OnlineMachine T key prec tw bw page q)
    (fixed addr seed : ℕ) (sizes : EntryWidths M fixed addr) (start : BootBodyWidth M seed) :
    SourceHeaderFit (borns M) fixed addr (sourceBodyCap s C seed) := by
  intro x p w
  obtain ⟨fixedFit,addrFit⟩ := sizes p w
  refine ⟨fixedFit,addrFit,?_⟩
  intro row inRows
  obtain ⟨h,_,eq⟩ := List.mem_map.mp inRows
  rw [←eq]
  exact actual_demanded_body_fits M seed start p w h

theorem demanded_job_is_the_next_scoped_record (M : OnlineMachine T key prec tw bw page q)
    (initial : L) (ready : ReadyOnStack (borns M) initial)
    (fixed addr seed : ℕ) (sizes : EntryWidths M fixed addr) (start : BootBodyWidth M seed)
    (p : Path sel r c) (u : (P).Slot c) (w : (P).Slot ((P).child c u)) :
    let path := Path.step p u
    let B := stackBank (borns M) initial path
    let K := M.demand (sourceState M p u) w
    let next := K.result.advance.next
    let j := next.birth.job
    let installed := j.install B
    installed=⟨(stackBank (borns M) initial (Path.step path w),true),
      publishFee B j.entry j.offset j.built⟩ ∧
    directoryBits installed.result.1=directoryBits B+insertionBits j ∧
    directoryBits installed.result.1≤descriptorBudget initial r.edges (pathLimit s C) fixed addr
      (sourceBodyCap s C seed) := by
  let path := Path.step p u
  let B := stackBank (borns M) initial path
  let K := M.demand (sourceState M p u) w
  let j := K.result.advance.next.birth.job
  have good : JobsReady B [j] := ready path w
  have op := (next_job_exact B j [] good).1
  have inserted := one_publication_adds_exact_directory_bits B j
  dsimp only
  refine ⟨op,?_,?_⟩
  · rw [op]
    exact inserted
  · rw [op]
    exact bounded_descriptor_stack_at_original_start (borns M) initial fixed addr (sourceBodyCap s C seed)
      (geometry_of_real_demand_caps_the_raw_header M fixed addr seed sizes start) (Path.step path w)

#print axioms geometry_of_real_demand_caps_the_raw_header
#print axioms demanded_job_is_the_next_scoped_record
end J6R51Peak
