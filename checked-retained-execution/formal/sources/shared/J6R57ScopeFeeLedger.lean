import J6R57ScopeFeeCaps
import J6R57ScopeFeeEntry
import J6R57ScopeFeeAtlas
import J6R57ScopeFeeRetire

/-! Feed the R56 phase-cap field a bound for its *actual* selected
scope. The only producer bounds are on the primitive boot/demand,
query/address generation and native source words, and on the
explicit numeric atlas tariff. No complete scope fee is assumed. -/
namespace J6R57ScopeFee
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R25PreparedSupply J6R26DescriptorTree
open J6ActiveRun J6ActiveSchedule J6R12Blueprint J6R11Blueprint J1PPrinted J6R16ModeCost
open J6R10Repack J6R24MeteredRecursion J6R34ChildPath
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS J6R49DFS J6R50SourceProducer J6R50Peak J6R51Peak J6R51Online
open J6R36ChildFramedRoute J6R41StructuredAllPaths J6R52Peak J6R52CacheWhole J6R53PeakAddon
open J6R55CachedLedger
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 24000000
set_option maxRecDepth 4800
set_option Elab.async false
noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "P" => (Plan sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)

structure PrimitiveCostCaps where
  boot : ℕ
  demand : ℕ
  queries : ℕ
  words : ℕ
  atlas : ℕ

structure PrimitiveCostFits (M : OnlineMachine T key prec tw bw page q)
    (V : PrimitiveCostCaps) : Prop where
  boot : ∀ w : (Plan sel).Slot r,(M.initial w).steps≤V.boot
  demand : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (u : (Plan sel).Slot x)
    (w : (Plan sel).Slot ((Plan sel).child x u)),(M.demand (sourceState M p u) w).steps≤V.demand
  query : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (u : (Plan sel).Slot x)
    (w : (Plan sel).Slot ((Plan sel).child x u)),
    sidecarQueryBill (M.demand (sourceState M p u) w).result≤V.queries
  words : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (Plan sel).Slot x),
    measuredWordProducers (sourceState M p w).input≤V.words
  atlas : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (Plan sel).Slot x),
    literalAtlasTariff (sourceState M p w).input≤V.atlas

def acquisitionCeiling (s rootEdges key prec page : ℕ) (W : ScopeWordCaps) (V : PrimitiveCostCaps) :=
  max (V.boot+uniformIndexGeometry s rootEdges key prec page W)
      (V.demand+V.queries+uniformDescSidecar s rootEdges key prec page W)

def derivedPerScope (s C rootEdges key prec tw bw page pointers nH nR : ℕ)
    (W : ScopeWordCaps) (V : PrimitiveCostCaps) : ℕ :=
  acquisitionCeiling s rootEdges key prec page W V+
    (V.words+entryGeometry rootEdges rootEdges W.fixed W.addr (sourceBodyCap s C W.seed) key+
    V.atlas+shapeFrameFee prec+
    livePublicationSetup s C rootEdges key prec tw bw W.fixed W.addr (sourceBodyCap s C W.seed)
      W.initialHeader nH nR+twoTailFee pointers+4)

theorem entry_geometry_mono_edges {m M n N : ℕ} (hM : m≤M) (hN : n≤N)
    (fixed addr body key : ℕ) :
    entryGeometry m n fixed addr body key≤entryGeometry M N fixed addr body key := by
  have scan := Nat.mul_le_mul_right (2*addr+3*body+81) (Nat.mul_le_mul_left 2 hM)
  have count := Nat.mul_le_mul_right (13*fixed+8) hN
  have ser := Nat.mul_le_mul_right (6*(addr+body)+5) hN
  have wires := Nat.mul_le_mul_right (addr+body) hN
  unfold entryGeometry
  omega

theorem actual_acquisition_meets_geometric_phase_cap
    (M : OnlineMachine T key prec tw bw page q) (initial : L)
    (W : ScopeWordCaps) (V : PrimitiveCostCaps) (hW : ScopeWordFits M initial W)
    (hV : PrimitiveCostFits M V) (p : Path sel r c) (w : (Plan sel).Slot c) :
    installedAddonDebit M p w≤acquisitionCeiling s r.edges key prec page W V := by
  cases p with
  | root =>
    exact (Nat.add_le_add (hV.boot w) (actual_first_index_at_uniform_width M initial W hW w)).trans
      (le_max_left _ _)
  | step p u =>
    let K := M.demand (sourceState M p u) w
    have own := actual_later_index_and_emit_at_uniform_width M initial W hW p u w
    have now : K.result.sidecarCharge≤V.queries+uniformDescSidecar s r.edges key prec page W :=
      own.trans (Nat.add_le_add_right (hV.query p u w) _)
    have pay : K.steps+K.result.sidecarCharge≤V.demand+V.queries+uniformDescSidecar s r.edges key prec page W := by
      have h := Nat.add_le_add (hV.demand p u w) now
      simpa only [Nat.add_assoc] using h
    exact pay.trans (le_max_right _ _)

theorem actual_cached_scope_has_derived_cap
    (M : OnlineMachine T key prec tw bw page q) (initial : L) {pointerWidth : ℕ}
    (tails : SavedDirectoryTails pointerWidth)
    (W : ScopeWordCaps) (V : PrimitiveCostCaps) (hW : ScopeWordFits M initial W)
    (hV : PrimitiveCostFits M V) (p : Path sel r c) (w : (Plan sel).Slot c) :
    cachedScopeOwn M (retireSavedDirectory tails) initial p w≤
      derivedPerScope s C r.edges key prec tw bw page pointerWidth initial.headers.length
        initial.records.length W V := by
  let B := borns M p w
  let bank := stackBank (borns M) initial p
  have build := compiled_occurrence_priced_by_actual_producers_and_chart (sourceState M p w).input
  have issued : B.issuance.steps≤V.words := by
    calc
      B.issuance.steps = measuredWordProducers (sourceState M p w).input := build.1
      _≤_ := hV.words p w
  have atlas : B.compilePages.steps≤V.atlas := build.2.trans (hV.atlas p w)
  have entry := actual_online_entry_ceiling M W.fixed W.addr W.seed hW.entry hW.boot p w
  have geom := entry_geometry_mono_edges (edge_width_of_actual_path p)
    (edge_width_of_actual_path (Path.step p w)) W.fixed W.addr (sourceBodyCap s C W.seed) key
  have bornEntry : B.job.entry.steps≤V.words+entryGeometry r.edges r.edges W.fixed W.addr
      (sourceBodyCap s C W.seed) key := entry.trans (Nat.add_le_add issued geom)
  have pub := actual_scope_publish_has_word_and_depth_ceiling M initial W.fixed W.addr W.seed
    W.initialHeader hW.entry hW.boot hW.headers p w
  have acq := actual_acquisition_meets_geometric_phase_cap M initial W V hW hV p w
  change installedAddonDebit M p w+(publishFee bank B.job.entry B.job.offset B.job.built+
    retireSavedDirectory tails B.job+4)≤_
  rw [retire_debit_is_the_fixed_handle_fee]
  unfold derivedPerScope
  change publishFee bank B.job.entry B.job.offset B.job.built≤
    B.job.entry.steps+B.compilePages.steps+shapeFrameFee prec+
      livePublicationSetup s C r.edges key prec tw bw W.fixed W.addr (sourceBodyCap s C W.seed)
        W.initialHeader initial.headers.length initial.records.length at pub
  omega

theorem derived_scope_phase_field
    (M : OnlineMachine T key prec tw bw page q) (initial : L) {pointerWidth : ℕ}
    (tails : SavedDirectoryTails pointerWidth)
    (W : ScopeWordCaps) (V : PrimitiveCostCaps) (hW : ScopeWordFits M initial W)
    (hV : PrimitiveCostFits M V) :
    ∀ (z : Sigma (Path sel r)) (w : (Plan sel).Slot z.1),
      cachedScopeOwn M (retireSavedDirectory tails) initial z.2 w≤
        derivedPerScope s C r.edges key prec tw bw page pointerWidth initial.headers.length
          initial.records.length W V :=
  fun z w=>actual_cached_scope_has_derived_cap M initial tails W V hW hV z.2 w

end
#print axioms entry_geometry_mono_edges
#print axioms actual_acquisition_meets_geometric_phase_cap
#print axioms actual_cached_scope_has_derived_cap
#print axioms derived_scope_phase_field
end J6R57ScopeFee
