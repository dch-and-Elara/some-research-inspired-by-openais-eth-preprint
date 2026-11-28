import J6R68ActiveInputsSweepLedger
import J6R68ActiveInputsSweepWidth
import J6R67UnifiedRateActive

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 26000000
set_option maxRecDepth 4200
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! The actual stock setup, selected-site weight tape and original-probe
masks all satisfy explicit numerical bounds on the same raw execution.
The remaining layout budget refers only to the real selected producer. -/
namespace J6R68ActiveInputs.Sweep
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R12 J6R22Active
open J6ActiveSchedule J6ActiveRun J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R49DFS J6R49Cost J6R50Peak
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R30ProducedGateRegistry
open J6R50SourceProducer J6R51Online J6R54PeakInput J6R53PeakAddon
open J6R48DFS J6R52Peak J6R51ParentFrames J6R52CacheWhole J6R48RawRoute J6R16ModeCost
open J6R58ActivePrep J6R62ActivePrep J6R63Active J6R64Active J6R66Active J6R67UnifiedRate
open J6R55CachedLedger J6R56PrintedExponent J6R57ActiveFee

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)

def sweptSetupPx (K layout : ℕ) := layout+sharedHeaderAndCopyRoof K+stockAdmissionPx K

def sweptActivePx (K layout : ℕ) :=
  activeNodeFixedPrice K (preparedCentrePx K) (mountedMaskPx K) (sweptSetupPx K layout)

structure SweepPhysicalFees
    {x : Call (PhysicalHost f ell)} {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) x}
    {bank : Bank f} (D : Meter (Schedule sel d bank q)) (K layout : ℕ) : Prop where
  high : x.prec+D.result.extra ≤ K
  setup : D.steps ≤ sweptSetupPx K layout
  tape : ∀ t,(D.result.proofView.tape t).tape.steps ≤ preparedCentrePx K
  mask : ∀ t z,((D.result.proofView.tape t).masks z).steps ≤ mountedMaskPx K

theorem exact_capture_and_stock_admission
    {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c} {pw eww n : ℕ}
    {valid : n ≤ 2^f.natDegree}
    (hq : 0<q) (fit : InputFits sel d q)
    (taperPos : 0<Shape.levelWidth S c.depth) (taperSmall : Shape.levelWidth S c.depth ≤ c.edges)
    (chart : MaskTable f.natDegree n valid) (cover : physicalProbeCount f ell s c ≤ n)
    (header : Meter (CallWords c pw eww)) (layout : Meter (AtLayout sel d cw))
    (K layoutCap : ℕ) (axis : Shape.levelBits S c.depth ≤ K)
    (taper : Shape.levelWidth S c.depth ≤ K) (mode : q ≤ K) (row : eww ≤ K)
    (grid : 2^(Shape.levelBits S c.depth+1) ≤ K)
    (shared : header.steps+(2*cw+4*q+5)+4 ≤ sharedHeaderAndCopyRoof K)
    (lay : layout.steps ≤ layoutCap) :
    (prepare (bank:=T.bank) hq fit taperPos taperSmall hf chart cover header layout).steps ≤ sweptSetupPx K layoutCap := by
  have act := prepare_bill_has_no_legacy_charge (bank:=T.bank) hq fit taperPos taperSmall hf chart cover header layout
  have stock := stock_admission_from_actual_dimensions axis taper mode row grid
  unfold sweptSetupPx
  omega

theorem actual_raw_path_has_derived_active_fields
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (E : RootInputs T key prec tw bw page cw ew) (initial : L) (own : OwnsHeader E.header initial)
    (p : Path sel r c) (a : (S).cutoff<c.edges) (K layoutCap : ℕ)
    (W : LiveHeaderFits M cw ew K)
    (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=q) (r:=r) K)
    (cs : PrintedCentreScale s C K)
    (rootRead : (E.inherit initial own).steps ≤ 20*K+13)
    (lay : currentLayoutDebit M F E initial own p a ≤ layoutCap)
    (absoluteHigh : absolutePrecision s r.edges r.prec+
      (C*s)*(24*2^(Nat.clog 2 s)+4*(Nat.clog 2 s+1)) ≤ K) :
    SweepPhysicalFees (rawScheduleAt M F chart E initial own p a) K layoutCap := by
  have oneCase {x : Call (PhysicalHost f ell)} (p : Path sel r x) (a : (S).cutoff<x.edges)
      {ww : ℕ} (H : Meter (CallWords x prec ww))
      (D : Meter (AtLayout sel (readyAtPath T p a) cw)) (we : ww ≤ K)
      (sh : H.steps+(2*cw+4*q+5)+4 ≤ sharedHeaderAndCopyRoof K) (dl : D.steps ≤ layoutCap) :
      let taper := actual_path_taper T p a
      SweepPhysicalFees (prepare (bank:=T.bank) M.modeWidth (F.fit p a) taper.1 taper.2
        hf chart.table (chart.covers p a) H D) K layoutCap := by
    let taper := actual_path_taper T p a
    let R := prepare (bank:=T.bank) M.modeWidth (F.fit p a) taper.1 taper.2
      hf chart.table (chart.covers p a) H D
    have frames := original_sweep_frame_dimensions (T:=T) p a M.modeWidth (F.fit p a) chart.table
      (chart.covers p a) H D K ws cs absoluteHigh
    have tapeMasks := true_sweep_selected_tapes_and_probes_are_bounded (T:=T) p a M.modeWidth (F.fit p a)
      chart.table (chart.covers p a) H D K ws cs W.precFit we
    have shape := actual_sweep_stock_grid_and_shape_fit (T:=T) p a K cs
    have setup := exact_capture_and_stock_admission (T:=T) M.modeWidth (F.fit p a) taper.1 taper.2 chart.table
      (chart.covers p a) H D K layoutCap ((Nat.le_succ _).trans shape.1) shape.2.1 ws.modeWord we shape.2.2 sh dl
    change SweepPhysicalFees R K layoutCap
    exact ⟨frames.2.2.1,setup,tapeMasks.2.1,tapeMasks.2.2⟩
  cases p with
  | root =>
    let here : Path sel r r := .root
    have shared : (E.inherit initial own).steps+(2*cw+4*q+5)+4 ≤ sharedHeaderAndCopyRoof K := by
      unfold sharedHeaderAndCopyRoof
      have cp := W.copyFit
      have mq := ws.modeWord
      omega
    exact oneCase here a (E.inherit initial own) (E.layout initial own a) W.extEdge shared lay
  | step p w =>
    let Y := sourceState M p w
    let live := stackBank (borns M) initial (.step p w)
    have ok : OwnsHeader Y.birth.job.entry.result live := rfl
    let H := readIncoming Y live ok
    have widths := W.desc p w
    have shared : H.steps+(2*cw+4*q+5)+4 ≤ sharedHeaderAndCopyRoof K := by
      change (readIncoming Y live ok).steps+_+4 ≤ _
      rw [(incoming_words_from_published_head Y live ok).2.2]
      exact true_header_and_retained_copy_roof W.precFit widths.1 widths.2.1 widths.2.2 W.copyFit ws.modeWord
    exact oneCase (.step p w) a H (F.layout p w Y a) widths.1 shared lay

theorem proof_view_mount_keeps_the_actual_resident_debit
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (E : RootInputs T key prec tw bw page cw ew) (initial : L) (own : OwnsHeader E.header initial)
    (p : Path sel r c) :
    cacheMountFee (proofDrivers M F chart E initial own) p=cacheMountFee M p := by
  let Q := proofDrivers M F chart E initial own
  cases p with
  | root => rfl
  | step p w =>
    change (mountResident (sourceState Q p w) (installResidentBank (sourceState Q p w)).result).steps=
      (mountResident (sourceState M p w) (installResidentBank (sourceState M p w)).result).steps
    rw [viewedDrivers_keep_actual_stored_sites]

theorem actual_swept_active_bill_is_affine
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (E : RootInputs T key prec tw bw page cw ew) (initial : L) (own : OwnsHeader E.header initial)
    (p : Path sel r c) (a : (S).cutoff<c.edges) (K seed layoutCap : ℕ)
    (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=q) (r:=r) K) (cs : PrintedCentreScale s C K)
    (mount : ActualMountWidths M K seed)
    (B : SweepPhysicalFees (rawScheduleAt M F chart E initial own p a) K layoutCap) :
    let Q := proofDrivers M F chart E initial own
    let A := preparedActive Q p a
    cacheMountFee Q p+A.steps+streamActiveTariff A.result (reachable_positive T p.reached) T.vPositive ≤
      sweptActivePx K layoutCap+physicalAddressUnit K*Nat.card ((P).Slot c) := by
  let Q := proofDrivers M F chart E initial own
  have prep := local_ledger_uses_the_same_raw_schedule M F chart E initial own p a
  have high : c.prec+(preparedActive Q p a).result.extraPrecision ≤ K := by
    rw [prep]
    exact B.high
  have tapes : ∀ t,((preparedActive Q p a).result.tape t).tape.steps ≤ preparedCentrePx K := by
    rw [prep]
    exact B.tape
  have masks : ∀ t z,(((preparedActive Q p a).result.tape t).masks z).steps ≤ mountedMaskPx K := by
    rw [prep]
    exact B.mask
  have setup : (preparedActive Q p a).steps ≤ sweptSetupPx K layoutCap := by
    rw [prep]
    exact B.setup
  have hMount : cacheMountFee Q p ≤ 256*(K+1)^3 := by
    rw [proof_view_mount_keeps_the_actual_resident_debit]
    exact actual_mount_caps_from_physical_words M K seed mount p
  exact actual_active_node_affine_with_paid_suppliers Q p a K (preparedCentrePx K) (mountedMaskPx K)
    (sweptSetupPx K layoutCap) (256*(K+1)^3) ws cs high tapes masks setup hMount
end

#print axioms exact_capture_and_stock_admission
#print axioms actual_raw_path_has_derived_active_fields
#print axioms proof_view_mount_keeps_the_actual_resident_debit
#print axioms actual_swept_active_bill_is_affine
end J6R68ActiveInputs.Sweep

