import J6R68ActiveInputsProducer
import J6R67UnifiedRateActive

/-! Exact selector-preserving R66/R67 attachment. The resulting
callbacks are the real ones passed to that runner; no fee transfer
from a stale independent chart and no second layout invocation. -/
namespace J6R68ActiveInputs
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape J6R10Repack
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint
open J6R12Blueprint J1PPrinted J6R15ModeCost J6R16ModeCost
open J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R21Ancestor J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R48DFS J6R49DFS J6R49Cost J6R50SourceProducer J6R51Online J6R55CachedLedger
open J6R14LayoutCost J6R17ModeTape J6R57ActiveFee J6R62ActivePrep J6R63Active J6R64Active J6R66Active
open J6R67UnifiedRate
open V8NativeMessage.N2DLabels

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 17000000
set_option maxRecDepth 3650
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s : ℕ} {c : Call (PhysicalHost f ell)}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s)
  (J6ActiveRun.Call.depth c))
local instance bindEdges : Fintype c.host.Edge := c.host.finiteEdge
local instance bindRows : Fintype c.host.Row := c.host.finiteRow
local instance bindCols : Fintype c.host.Col := c.host.finiteCol

structure ChosenSetup (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
    (d : Ready SP (sourceDelta s) c) (rank : ℕ) where
  input : CallFormat SP c
  bytes : Ingress input
  pos : 0<rank
  dim : A ≤ rank
  fit : c.edges<2^rank
  coordinate : ∀ w,input.format.label w=coordinateLabel w
  exactLabels : input.run.result.1=input.format.graph (fun v=>some (wordsOf (packing sel d) v))
  rounding : RoundsExactly (packing sel d)
  measured : input.run.steps ≤ input.fee

def setupForFull64 (inputs : Full64PlanInputs SP (sourceDelta s))
    (d : Ready SP (sourceDelta s) c) (rank : ℕ) (pos : 0<rank)
    (dim : A ≤ rank) (fit : c.edges<2^rank)
    (coord : ∀ w,(inputs c d).format.label w=coordinateLabel w) (bytes : Ingress (inputs c d)) :
    ChosenSetup (forget (full64Selector inputs)) d rank :=
  let selected := full64_selected_receipt inputs d
  ⟨inputs c d,bytes,pos,dim,fit,coord,selected.2.2.2.1,selected.2.1,selected.2.2.2.2⟩

variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c} {rank : ℕ}

def transportLayout {i j a b w : ℕ} (eq : i=j) (R : Meter (LayoutReceipt a b w i)) :
    Meter (LayoutReceipt a b w j) :=
  eq ▸ R

theorem transportLayout_steps {i j a b w : ℕ} (eq : i=j) (R : Meter (LayoutReceipt a b w i)) :
    (transportLayout eq R).steps=R.steps := by
  subst j
  rfl

def ChosenSetup.run (W : ChosenSetup (c:=c) sel d rank) : Meter (AtLayout (c:=c) sel d (rank+1)) :=
  let countEq : Fintype.card c.host.Edge=c.edges := layout_actual_edge_count (s:=s) (c:=c) d
  let rawFit : Fintype.card c.host.Edge<2^rank :=
    Eq.mpr (congrArg (fun j : ℕ=>j<2^rank) countEq) W.fit
  transportLayout countEq (paidSelectedSetup W.input (packing sel d) rank W.pos W.dim
    rawFit W.coordinate W.exactLabels W.rounding W.bytes)

theorem chosen_setup_uniform (W : ChosenSetup (c:=c) sel d rank) (K ingressCap : ℕ)
    (shape : LayoutScales W.input rank K) (pay : W.bytes.paid.steps ≤ ingressCap) :
    W.run.steps ≤ ingressCap+selectedLayoutRoof K+3 := by
  unfold ChosenSetup.run
  dsimp only
  rw [transportLayout_steps]
  let counts : Fintype.card c.host.Edge=c.edges := layout_actual_edge_count (s:=s) (c:=c) d
  have slots : 2^A*J9PrintedSchedule.arrayCard A ≤ Fintype.card c.host.Edge :=
    counts.symm ▸ d.paddedSlots
  exact (physical_layout_setup_has_uniform_fee W.input (packing sel d) rank K W.pos W.dim
    (Eq.mpr (congrArg (fun j : ℕ=>j<2^rank) counts) W.fit) W.coordinate W.exactLabels W.rounding W.bytes W.measured shape slots).2.trans
    (Nat.add_le_add_right (Nat.add_le_add_right pay _) _)

variable {C key prec tw bw page q ew : ℕ} {cfg : RootBounds s C f}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Here" => (Path.root : Path sel r r)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)

/-- The incoming site is used before there exists an outgoing slot of
the new active call. The exterior entry carries a distinct source. -/
structure CurrentLayoutSources (T : Prepared cfg sel r hf) (key prec tw bw page rank : ℕ)
    (header : DirRow key) where
  exterior : (B : PageBank f ell key prec tw bw page) → OwnsHeader header B →
    (a : (SP).cutoff<r.edges) → ChosenSetup sel (readyAtPath T Here a) rank
  after : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (P).Slot x),
    StoredSite T (p.ticket w) key prec tw bw page →
    (a : (SP).cutoff<((P).child x w).edges) → ChosenSetup sel (readyAtPath T (.step p w) a) rank

variable {header : DirRow key}

def CurrentLayoutSources.rootInputs (D : CurrentLayoutSources T key prec tw bw page rank header)
    (inherit : (B : L) → OwnsHeader header B → Meter (CallWords r prec ew)) :
    RootInputs T key prec tw bw page (rank+1) ew :=
  ⟨header,inherit,fun B own a=>(D.exterior B own a).run⟩

def CurrentLayoutSources.retained (D : CurrentLayoutSources T key prec tw bw page rank header)
    (fit : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (a : (SP).cutoff<x.edges),
      InputFits sel (readyAtPath T p a) q) :
    RetainedAfter T key prec tw bw page q (rank+1) :=
  ⟨fit,fun p w X a=>(D.after p w X a).run⟩

def CurrentLayoutSources.atPath (D : CurrentLayoutSources T key prec tw bw page rank header)
    (M : Machine) (B : L) (own : OwnsHeader header B) :
    {x : Call (PhysicalHost f ell)} → (p : Path sel r x) → (a : (SP).cutoff<x.edges) →
      ChosenSetup sel (readyAtPath T p a) rank
  | _,.root,a => D.exterior B own a
  | _,.step p w,a => D.after p w (sourceState M p w) a

theorem actual_current_debit_is_the_paid_greedy_step
    (D : CurrentLayoutSources T key prec tw bw page rank header)
    (M : Machine) (B : L) (own : OwnsHeader header B)
    (inherit : (B : L) → OwnsHeader header B → Meter (CallWords r prec ew))
    (fit : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (a : (SP).cutoff<x.edges),
      InputFits sel (readyAtPath T p a) q)
    (p : Path sel r c) (a : (SP).cutoff<c.edges) :
    currentLayoutDebit M (D.retained fit) (D.rootInputs inherit) B own p a=
      (D.atPath M B own p a).run.steps := by
  cases p <;> rfl

theorem live_affine_uses_paid_greedy_without_a_layout_cap
    (D : CurrentLayoutSources T key prec tw bw page rank header)
    (M : Machine) (B : L) (own : OwnsHeader header B)
    (inherit : (B : L) → OwnsHeader header B → Meter (CallWords r prec ew))
    (fit : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (a : (SP).cutoff<x.edges),
      InputFits sel (readyAtPath T p a) q)
    (p : Path sel r c) (a : (SP).cutoff<c.edges)
    (K seed baseBudget ingressCap mask : ℕ)
    (W : LiveHeaderFits M (rank+1) ew K)
    (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=q) (r:=r) K)
    (cs : PrintedCentreScale s C K) (mount : ActualMountWidths M K seed)
    (rootRead : (inherit B own).steps ≤ 20*K+13)
    (oldBase : (preparedActive M p a).steps ≤ baseBudget)
    (shape : LayoutScales (D.atPath M B own p a).input rank K)
    (rawDebit : (D.atPath M B own p a).bytes.paid.steps ≤ ingressCap)
    (high : c.prec+(preparedActive M p a).result.extraPrecision ≤ K)
    (masks : ∀ t z,(((preparedActive M p a).result.tape t).masks z).steps ≤ mask) :
    let Dₐ := liveActiveAt M (D.retained fit) (D.rootInputs inherit) B own p a
    cacheMountFee M p+Dₐ.steps+streamActiveTariff Dₐ.result
      (reachable_positive T p.reached) T.vPositive ≤ activeNodeFixedPrice K (liveActiveTapeRoof K) mask
        (baseBudget+(ingressCap+selectedLayoutRoof K+3)+sharedHeaderAndCopyRoof K)+
          physicalAddressUnit K*Nat.card ((P).Slot c) := by
  apply actual_active_affine_from_paid_dimensions M (D.retained fit) (D.rootInputs inherit) B own p a
    K seed baseBudget (ingressCap+selectedLayoutRoof K+3) mask W ws cs mount rootRead oldBase
    _ high masks
  rw [actual_current_debit_is_the_paid_greedy_step D M B own inherit fit p a]
  exact chosen_setup_uniform (D.atPath M B own p a) K ingressCap shape rawDebit

#print axioms setupForFull64
#print axioms chosen_setup_uniform
#print axioms actual_current_debit_is_the_paid_greedy_step
#print axioms live_affine_uses_paid_greedy_without_a_layout_cap
end
end J6R68ActiveInputs
