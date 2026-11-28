import J6R68ActiveInputsSweepCompare
import J6R66ActiveLedger
import J6R56PrintedExponentPhases
import J6R68AbsolutePrescribedLedger

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 29000000
set_option maxRecDepth 4100
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! Equality of full meters joins the new raw sweep to the existing
occurrence ledger. The proof shadow is defined from this sweep, not
an assumption about the original arbitrary active supplier. -/
namespace J6R68ActiveInputs.Sweep
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R12 J6R22Active
open J6R64Active J6R62ActivePrep J6R66Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R49Cost J6R51
open J6R51Online J6R52CacheWhole J6R52Peak J6R53PeakAddon J6R54PeakInput
open J6R55CachedLedger J6R56PrintedExponent J6R68AbsolutePrescribed

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
local notation "H" => (J9PrintedSchedule.leafThreshold s (Nat.clog 2 s))
local notation "Here" => (Path.root : Path sel r r)

def rawScheduleAt (M : Machine) (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (E : RootInputs T key prec tw bw page cw ew)
    (initial : L) (rootOwn : OwnsHeader E.header initial) :
    {x : Call (PhysicalHost f ell)} → (p : Path sel r x) → (a : (S).cutoff<x.edges) →
      Meter (Schedule sel (readyAtPath T p a) T.bank q)
  | _, .root,a => rootPrepare M F chart E initial rootOwn a
  | _, .step p w,a =>
      let X := sourceState M p w
      let bank := stackBank (borns M) initial (.step p w)
      afterPrepare M F chart p w X bank rfl a

theorem local_ledger_uses_the_same_raw_schedule
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (E : RootInputs T key prec tw bw page cw ew) (initial : L) (own : OwnsHeader E.header initial)
    (p : Path sel r c) (a : (S).cutoff<c.edges) :
    preparedActive (proofDrivers M F chart E initial own) p a=viewOf (rawScheduleAt M F chart E initial own p a) := by
  let Q := proofDrivers M F chart E initial own
  cases p with
  | root => rfl
  | step p w =>
    change viewOf (afterPrepare M F chart p w (sourceState Q p w)
      (headNormalForm (sourceState Q p w)) rfl a)=
      viewOf (afterPrepare M F chart p w (sourceState M p w) (stackBank (borns M) initial (.step p w)) rfl a)
    rw [viewedDrivers_keep_actual_stored_sites]
    let X := sourceState M p w
    let live := stackBank (borns M) initial (.step p w)
    have entered : OwnsHeader X.birth.job.entry.result live := rfl
    exact congrArg viewOf (real_stock_setup_independent_of_directory_tail M F chart p w X live
      (headNormalForm X) entered rfl a).symm

theorem raw_scope_keeps_original_own_fee (M : Machine)
    (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (E : RootInputs T key prec tw bw page cw ew) (initial : L) (own : OwnsHeader E.header initial)
    (retire : J→ℕ) (p : Path sel r c) (w : (P).Slot c) :
    cachedScopeOwn (proofDrivers M F chart E initial own) retire initial p w=cachedScopeOwn M retire initial p w := by
  let Q := proofDrivers M F chart E initial own
  unfold cachedScopeOwn
  dsimp only
  rw [viewedDrivers_keep_actual_births]
  have debit : installedAddonDebit Q p w=installedAddonDebit M p w := by
    cases p with
    | root =>
      change (M.initial w).steps+(installResidentBank (sourceState Q .root w)).steps=
        (M.initial w).steps+(installResidentBank (sourceState M .root w)).steps
      rw [viewedDrivers_keep_actual_stored_sites]
    | step p prior =>
      change paidAcquisition (M.demand (sourceState Q p prior) w)=
        paidAcquisition (M.demand (sourceState M p prior) w)
      rw [viewedDrivers_keep_actual_stored_sites]
  rw [debit]

theorem raw_local_ledger_uses_the_actual_meter (M : Machine)
    (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (E : RootInputs T key prec tw bw page cw ew) (initial : L) (own : OwnsHeader E.header initial)
    (retire : J→ℕ) (p : Path sel r c) (a : (S).cutoff<c.edges) :
    let Q := proofDrivers M F chart E initial own
    let A := rawScheduleAt M F chart E initial own p a
    letI : Fintype ((P).Slot c) := (P).finiteSlot c
    cachedOwn Q retire initial ⟨c,p⟩=cacheMountFee Q p+A.steps+
      streamActiveTariff A.result.proofView (reachable_positive T p.reached) T.vPositive+
      ∑ w : (P).Slot c,cachedScopeOwn M retire initial p w := by
  dsimp only
  rw [cachedOwn,dif_neg (Nat.not_le.mpr a),local_ledger_uses_the_same_raw_schedule]
  letI : Fintype ((P).Slot c) := (P).finiteSlot c
  have h : (∑ w : (P).Slot c,cachedScopeOwn (proofDrivers M F chart E initial own) retire initial p w)=
      ∑ w : (P).Slot c,cachedScopeOwn M retire initial p w := by
    apply Finset.sum_congr rfl
    intro w _
    exact raw_scope_keeps_original_own_fee M F chart E initial own retire p w
  rw [h]
  rfl

theorem raw_view_leaf_reads_the_same_meter
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (E : RootInputs T key prec tw bw page cw ew) (initial : L) (own : OwnsHeader E.header initial)
    (p : Path sel r c) (stop : c.edges ≤ (S).cutoff) :
    readLeaf (proofDrivers M F chart E initial own) initial p stop=readLeaf M initial p stop := by
  let Q := proofDrivers M F chart E initial own
  cases p with
  | root => rfl
  | step p w =>
    change M.leafAfter p w (sourceState Q p w) stop (stackBank (borns Q) initial (.step p w))=
      M.leafAfter p w (sourceState M p w) stop (stackBank (borns M) initial (.step p w))
    rw [viewedDrivers_keep_actual_stored_sites,viewedDrivers_keep_actual_births]

variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem raw_view_leaves_agree
    [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r)]
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (E : RootInputs T key prec tw bw page cw ew) (initial : L) (own : OwnsHeader E.header initial)
    (leaves : LeafAgreement M initial) : LeafAgreement (proofDrivers M F chart E initial own) initial := by
  let Q := proofDrivers M F chart E initial own
  refine ⟨leaves.root,?_⟩
  intro c p w stop
  change (T.frame (Path.step p w).reached).decode
    (M.leafAfter p w (sourceState Q p w) stop (stackBank (borns Q) initial (.step p w))).result=_
  rw [viewedDrivers_keep_actual_stored_sites,viewedDrivers_keep_actual_births]
  exact leaves.after p w stop

theorem actual_raw_contraction_and_occurrence_bill
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (E : RootInputs T key prec tw bw page cw ew) (retire : J→ℕ)
    (initial : L) (own : OwnsHeader E.header initial) (legal : ReadyOnStack (borns M) initial)
    (leaves : letI : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r) :=
      J6R24MeteredRecursion.sourceDecision sel r; LeafAgreement M initial)
    (rootFit : r.depth≤pathLimit s C) :
    let out := runRawRoot M F chart E retire initial own
    (T.frame (Here).reached).decode out.result.1=
      reduce r.prec f ell (r.host.contract hf) ∧ out.result.2=initial ∧
      out.steps≤∑ j ∈ Finset.range (pathLimit s C-r.depth+1),
        levelBill (nativeScopedPlan sel r) ⟨r,Here⟩
          (cachedOwn (proofDrivers M F chart E initial own) retire initial) j := by
  letI : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r) :=
    J6R24MeteredRecursion.sourceDecision sel r
  let Q := proofDrivers M F chart E initial own
  have ok : ReadyOnStack (borns Q) initial := by
    change ReadyOnStack (borns (proofDrivers M F chart E initial own)) initial
    rw [viewedDrivers_keep_actual_births]
    exact legal
  dsimp only
  rw [root_matches_own_proof_meter]
  exact same_single_emission_exact_contraction_and_actual_occurrence_bill Q retire initial ok
    (raw_view_leaves_agree M F chart E initial own leaves) rootFit

theorem actual_raw_sweep_run_from_prescribed_seed
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (E : RootInputs T key prec tw bw page cw ew) (retire : J→ℕ)
    (initial : L) (own : OwnsHeader E.header initial) (legal : ReadyOnStack (borns M) initial)
    (leaves : letI : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r) :=
      J6R24MeteredRecursion.sourceDecision sel r; LeafAgreement M initial)
    (seed : AbsoluteSeed s C r)
    (fixed arithmetic perScope scale localPower : ℕ)
    (caps : CachedThreePhaseCaps (proofDrivers M F chart E initial own) retire initial fixed arithmetic perScope)
    (localBound : fixed+(arithmetic+perScope)≤scale*2^(localPower*H)) :
    let out := runRawRoot M F chart E retire initial own
    (T.frame (Here).reached).decode out.result.1=
      reduce r.prec f ell (r.host.contract hf) ∧ out.result.2=initial ∧
      out.steps≤(pathLimit s C-r.depth+1)*scale*2^((fullPrefixConstant C+localPower)*H) := by
  let Q := nativeScopedPlan sel r
  let lam := Nat.clog 2 s
  let root := Sigma.mk r (Here)
  let source := proofDrivers M F chart E initial own
  let out := runRawRoot M F chart E retire initial own
  obtain ⟨value,restored,bill⟩ :=
    actual_raw_contraction_and_occurrence_bill M F chart E retire initial own legal leaves seed.depth
  refine ⟨value,restored,?_⟩
  let addresses := arithmetic+perScope
  have affine := actual_cached_affine_from_phase_caps source retire initial fixed arithmetic perScope caps
  have total :
      out.steps≤(pathLimit s C-r.depth+1)*(fixed+addresses)*2^(fullPrefixConstant C*H) := by
    apply compress_absolute_meter_bound s C r.depth _ _ cfg.constPos cfg.size (root_lambda_large cfg)
    apply bill.trans
    let fan := actual_scoped_fanout_from_prescribed (cfg:=cfg) (sel:=sel) seed
    exact total_fee_bound Q root s C lam (siteConstant C) (branchBits lam)
      (pathLimit s C-r.depth+1) (fixed+addresses) (cachedOwn source retire initial)
      fan (fun j z seen=>local_charge_affine_le (affine z) (fan j z seen))
  refine total.trans ?_
  calc
    _≤(pathLimit s C-r.depth+1)*(scale*2^(localPower*H))*2^(fullPrefixConstant C*H) :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ localBound)
    _=_ := by rw [Nat.add_mul (fullPrefixConstant C) localPower H,pow_add]; ring

#print axioms local_ledger_uses_the_same_raw_schedule
#print axioms raw_scope_keeps_original_own_fee
#print axioms raw_local_ledger_uses_the_actual_meter
#print axioms raw_view_leaf_reads_the_same_meter
#print axioms raw_view_leaves_agree
#print axioms actual_raw_contraction_and_occurrence_bill
#print axioms actual_raw_sweep_run_from_prescribed_seed
end
end J6R68ActiveInputs.Sweep
