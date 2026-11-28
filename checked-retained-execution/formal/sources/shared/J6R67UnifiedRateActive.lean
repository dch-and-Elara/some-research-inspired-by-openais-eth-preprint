import J6R67UnifiedRateFee
import J6R57ActiveFeeCombine

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 19000000
set_option maxRecDepth 3900
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! Put the finite tape and current header bounds into the actual
R66 active phase. The still-external base/retained-layout debits and
monitorable high/mask fields are explicitly distinguished. -/
namespace J6R67UnifiedRate
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R57ActiveFee J6R63Active J6R64Active J6R62ActivePrep J6R66Active J6R55CachedLedger
open J6R50SourceProducer J6R51Online J6R49Cost J6R30ProducedGateRegistry

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)

structure LiveHeaderFits (M : Machine) (copyW edgeW K : ℕ) : Prop where
  precFit : prec≤K
  copyFit : copyW≤K
  extEdge : edgeW≤K
  desc : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (P).Slot x),
    let X := sourceState M p w
    X.birth.edge≤K ∧ X.birth.dep≤K ∧ X.birth.job.offset≤K

def currentLayoutDebit (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (B : L) (own : OwnsHeader E.header B) :
    {x : Call (PhysicalHost f ell)} → (p : Path sel r x) → (a : (S).cutoff<x.edges) → ℕ
  | _,.root,a => (E.layout B own a).steps
  | _,.step p w,a => (F.layout p w (sourceState M p w) a).steps

theorem live_active_keeps_base_hi_and_masks
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (B : L) (own : OwnsHeader E.header B)
    (p : Path sel r c) (a : (S).cutoff<c.edges) :
    let A := liveActiveAt M F E B own p a
    let D := preparedActive M p a
    A.result.extraPrecision=D.result.extraPrecision ∧
      (∀ t z, (A.result.tape t).masks z=(D.result.tape t).masks z) := by
  cases p <;> exact ⟨rfl,fun _ _=>rfl⟩

theorem actual_active_shared_tapes_fit_roof
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (B : L) (own : OwnsHeader E.header B)
    (p : Path sel r c) (a : (S).cutoff<c.edges) (t : Center S c)
    (K : ℕ) (W : LiveHeaderFits M cw ew K)
    (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=q) (r:=r) K)
    (cs : PrintedCentreScale s C K) :
    ((liveActiveAt M F E B own p a).result.tape t).tape.steps≤liveActiveTapeRoof K := by
  cases p with
  | root =>
    let entrance : Path sel r r := .root
    exact real_shared_tape_from_numeric_dimensions T entrance a t M.modeWidth (F.fit entrance a)
      (E.inherit B own) (E.layout B own a) (M.activeRoot a) K ws cs W.precFit W.extEdge
  | step p w =>
    let X := sourceState M p w
    let live := stackBank (borns M) B (.step p w)
    have ok : OwnsHeader X.birth.job.entry.result live := rfl
    exact real_shared_tape_from_numeric_dimensions T (.step p w) a t M.modeWidth
      (F.fit (.step p w) a) (readIncoming X live ok) (F.layout p w X a)
      (M.activeAfter p w X a) K ws cs W.precFit (W.desc p w).1

theorem actual_live_setup_from_separate_paid_sources
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (B : L) (own : OwnsHeader E.header B)
    (p : Path sel r c) (a : (S).cutoff<c.edges)
    (K baseBudget layoutBudget : ℕ) (W : LiveHeaderFits M cw ew K) (hq : q≤K)
    (rootRead : (E.inherit B own).steps≤20*K+13)
    (oldBase : (preparedActive M p a).steps≤baseBudget)
    (lay : currentLayoutDebit M F E B own p a≤layoutBudget) :
    (liveActiveAt M F E B own p a).steps≤baseBudget+layoutBudget+sharedHeaderAndCopyRoof K := by
  cases p with
  | root =>
    let entrance : Path sel r r := .root
    let tape := actual_path_taper T entrance a
    change (M.activeRoot a).steps≤baseBudget at oldBase
    change (E.layout B own a).steps≤layoutBudget at lay
    change (sharedMachine M.modeWidth (F.fit entrance a) tape.1 tape.2
      (E.inherit B own) (E.layout B own a) (M.activeRoot a)).steps≤_
    rw [(shared_setup_has_one_header_and_one_layout M.modeWidth (F.fit entrance a) tape.1 tape.2
      (E.inherit B own) (E.layout B own a) (M.activeRoot a)).1]
    have copy := W.copyFit
    unfold sharedHeaderAndCopyRoof
    omega
  | step p w =>
    let X := sourceState M p w
    let live := stackBank (borns M) B (.step p w)
    have ok : OwnsHeader X.birth.job.entry.result live := rfl
    change (M.activeAfter p w X a).steps≤baseBudget at oldBase
    change (F.layout p w X a).steps≤layoutBudget at lay
    change (preparedAfter M F.live p w X live ok a).steps≤_
    rw [physical_after_setup_charge M F.live p w X live ok a]
    change (M.activeAfter p w X a).steps+
      (callReadFee prec X.birth.edge X.birth.dep X.birth.job.offset+5)+
      (F.layout p w X a).steps+(2*cw+4*q+5)+4≤_
    have widths := W.desc p w
    have extra := true_header_and_retained_copy_roof W.precFit widths.1 widths.2.1 widths.2.2 W.copyFit hq
    change (callReadFee prec X.birth.edge X.birth.dep X.birth.job.offset+5)+(2*cw+4*q+5)+4≤_ at extra
    omega

theorem actual_active_affine_from_paid_dimensions
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (B : L) (own : OwnsHeader E.header B)
    (p : Path sel r c) (a : (S).cutoff<c.edges)
    (K seed baseBudget layoutBudget mask : ℕ)
    (W : LiveHeaderFits M cw ew K)
    (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=q) (r:=r) K)
    (cs : PrintedCentreScale s C K) (mount : ActualMountWidths M K seed)
    (rootRead : (E.inherit B own).steps≤20*K+13)
    (oldBase : (preparedActive M p a).steps≤baseBudget)
    (lay : currentLayoutDebit M F E B own p a≤layoutBudget)
    (high : c.prec+(preparedActive M p a).result.extraPrecision≤K)
    (masks : ∀ t z,(((preparedActive M p a).result.tape t).masks z).steps ≤ mask) :
    let A := liveActiveAt M F E B own p a
    cacheMountFee M p+A.steps+streamActiveTariff A.result
      (reachable_positive T p.reached) T.vPositive≤
      activeNodeFixedPrice K (liveActiveTapeRoof K) mask
        (baseBudget+layoutBudget+sharedHeaderAndCopyRoof K)+
          physicalAddressUnit K*Nat.card ((P).Slot c) := by
  let Q := shadow M F E B own
  have prepEq := local_schedule_reads_exact_active_preparation M F E B own p a
  have mountEq := original_cache_mount_fee_is_unchanged M F E B own p
  have fields := live_active_keeps_base_hi_and_masks M F E B own p a
  have hHigh : c.prec+(preparedActive Q p a).result.extraPrecision≤K := by
    rw [prepEq,fields.1]
    exact high
  have hTape (t : Center S c) :
      ((preparedActive Q p a).result.tape t).tape.steps≤liveActiveTapeRoof K := by
    rw [prepEq]
    exact actual_active_shared_tapes_fit_roof M F E B own p a t K W ws cs
  have hMask (t : Center S c) (z : Probe S c) :
      (((preparedActive Q p a).result.tape t).masks z).steps≤mask := by
    rw [prepEq,fields.2 t z]
    exact masks t z
  have hPrep : (preparedActive Q p a).steps≤baseBudget+layoutBudget+sharedHeaderAndCopyRoof K := by
    rw [prepEq]
    exact actual_live_setup_from_separate_paid_sources M F E B own p a K baseBudget layoutBudget W
      ws.modeWord rootRead oldBase lay
  have hMount : cacheMountFee Q p≤256*(K+1)^3 := by
    rw [mountEq]
    exact actual_mount_caps_from_physical_words M K seed mount p
  have result := actual_active_node_affine_with_paid_suppliers Q p a K (liveActiveTapeRoof K) mask
    (baseBudget+layoutBudget+sharedHeaderAndCopyRoof K) (256*(K+1)^3) ws cs hHigh hTape hMask hPrep hMount
  dsimp only at result ⊢
  rw [prepEq,mountEq] at result
  exact result

#print axioms currentLayoutDebit
#print axioms live_active_keeps_base_hi_and_masks
#print axioms actual_active_shared_tapes_fit_roof
#print axioms actual_live_setup_from_separate_paid_sources
#print axioms actual_active_affine_from_paid_dimensions
end
end J6R67UnifiedRate

