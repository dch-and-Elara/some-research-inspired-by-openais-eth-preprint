import J6R66ActiveCompare
import J6R56PrintedExponentPhases

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 29000000
set_option maxRecDepth 4100
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! Local charges and the whole occurrence schedule are from the very
same run proved in Compare. Existing leaves, sidecar acquisition,
publisher and retirement are unchanged; the installed active words
and tape are accounted under their actual replacement preparer. -/
namespace J6R66Active
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R12 J6R22Active
open J6R64Active J6R62ActivePrep
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R49Cost J6R51
open J6R51Online J6R52CacheWhole J6R52Peak J6R53PeakAddon J6R54PeakInput
open J6R55CachedLedger J6R56PrintedExponent

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

def liveActiveAt (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew)
    (initial : L) (rootOwn : OwnsHeader E.header initial) :
    {x : Call (PhysicalHost f ell)} → (p : Path sel r x) → (a : (S).cutoff<x.edges) →
      Meter (ActiveMachine sel (readyAtPath T p a) T.bank q)
  | _, .root,a => rootSetup M F E initial rootOwn a
  | _, .step p w,a =>
      let X := sourceState M p w
      let bank := stackBank (borns M) initial (.step p w)
      preparedAfter M F.live p w X bank rfl a

theorem local_schedule_reads_exact_active_preparation
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (initial : L) (own : OwnsHeader E.header initial)
    (p : Path sel r c) (a : (S).cutoff<c.edges) :
    preparedActive (shadow M F E initial own) p a=liveActiveAt M F E initial own p a := by
  let Q := shadow M F E initial own
  cases p with
  | root => rfl
  | step p w =>
    change summaryAfter M F p w (sourceState Q p w) a=
      preparedAfter M F.live p w (sourceState M p w) (stackBank (borns M) initial (.step p w)) rfl a
    rw [shadow_stored_sites_unchanged]
    let X := sourceState M p w
    let live := stackBank (borns M) initial (.step p w)
    have entered : OwnsHeader X.birth.job.entry.result live := rfl
    exact (real_preparation_is_exact_header_normal_form M F p w X live entered a).symm

theorem actual_scope_keeps_original_own_fee (M : Machine)
    (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (initial : L) (own : OwnsHeader E.header initial)
    (retire : J→ℕ) (p : Path sel r c) (w : (P).Slot c) :
    cachedScopeOwn (shadow M F E initial own) retire initial p w=cachedScopeOwn M retire initial p w := by
  let Q := shadow M F E initial own
  unfold cachedScopeOwn
  dsimp only
  rw [shadow_births_unchanged]
  have debit : installedAddonDebit Q p w=installedAddonDebit M p w := by
    cases p with
    | root =>
      change (M.initial w).steps+(installResidentBank (sourceState Q .root w)).steps=
        (M.initial w).steps+(installResidentBank (sourceState M .root w)).steps
      rw [shadow_stored_sites_unchanged]
    | step p prior =>
      change paidAcquisition (M.demand (sourceState Q p prior) w)=
        paidAcquisition (M.demand (sourceState M p prior) w)
      rw [shadow_stored_sites_unchanged]
  rw [debit]

theorem active_local_ledger_uses_the_live_meter (M : Machine)
    (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (initial : L) (own : OwnsHeader E.header initial)
    (retire : J→ℕ) (p : Path sel r c) (a : (S).cutoff<c.edges) :
    let Q := shadow M F E initial own
    let A := liveActiveAt M F E initial own p a
    letI : Fintype ((P).Slot c) := (P).finiteSlot c
    cachedOwn Q retire initial ⟨c,p⟩=cacheMountFee Q p+A.steps+
      streamActiveTariff A.result (reachable_positive T p.reached) T.vPositive+
      ∑ w : (P).Slot c,cachedScopeOwn M retire initial p w := by
  dsimp only
  rw [cachedOwn,dif_neg (Nat.not_le.mpr a),local_schedule_reads_exact_active_preparation]
  letI : Fintype ((P).Slot c) := (P).finiteSlot c
  have h : (∑ w : (P).Slot c,cachedScopeOwn (shadow M F E initial own) retire initial p w)=
      ∑ w : (P).Slot c,cachedScopeOwn M retire initial p w := by
    apply Finset.sum_congr rfl
    intro w _
    exact actual_scope_keeps_original_own_fee M F E initial own retire p w
  rw [h]

variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem leaves_same_for_actual_ledger
    [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r)]
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (initial : L) (own : OwnsHeader E.header initial)
    (leaves : LeafAgreement M initial) : LeafAgreement (shadow M F E initial own) initial := by
  let Q := shadow M F E initial own
  refine ⟨leaves.root,?_⟩
  intro c p w stop
  change (T.frame (Path.step p w).reached).decode
    (M.leafAfter p w (sourceState Q p w) stop (stackBank (borns Q) initial (.step p w))).result=_
  rw [shadow_stored_sites_unchanged,shadow_births_unchanged]
  exact leaves.after p w stop

theorem same_real_run_exact_output_and_occurrence_bill
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (retire : J→ℕ)
    (initial : L) (own : OwnsHeader E.header initial) (legal : ReadyOnStack (borns M) initial)
    (leaves : letI : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r) :=
      J6R24MeteredRecursion.sourceDecision sel r; LeafAgreement M initial)
    (rootFit : r.depth≤pathLimit s C) :
    let out := runRoot M F E retire initial own
    (T.frame (Here).reached).decode out.result.1=
      reduce r.prec f ell (r.host.contract hf) ∧ out.result.2=initial ∧
      out.steps≤∑ j ∈ Finset.range (pathLimit s C-r.depth+1),
        levelBill (nativeScopedPlan sel r) ⟨r,Here⟩
          (cachedOwn (shadow M F E initial own) retire initial) j := by
  letI : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r) :=
    J6R24MeteredRecursion.sourceDecision sel r
  let Q := shadow M F E initial own
  have ok : ReadyOnStack (borns Q) initial := by
    change ReadyOnStack (borns (shadow M F E initial own)) initial
    rw [shadow_births_unchanged]
    exact legal
  dsimp only
  rw [same_actual_root_meter]
  exact same_single_emission_exact_contraction_and_actual_occurrence_bill Q retire initial ok
    (leaves_same_for_actual_ledger M F E initial own leaves) rootFit

theorem actual_run_r56_caps
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (retire : J→ℕ)
    (initial : L) (own : OwnsHeader E.header initial) (legal : ReadyOnStack (borns M) initial)
    (leaves : letI : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r) :=
      J6R24MeteredRecursion.sourceDecision sel r; LeafAgreement M initial)
    (fit : r.depth≤pathLimit s C) {anchor : Call (PhysicalHost f ell)}
    (stable : Stable s C anchor) (zero : anchor.depth=0) (anchorPrec : anchor.prec≤C*s)
    (link : NativeReach (Plan sel) anchor r)
    (fixed arithmetic perScope scale localPower : ℕ)
    (caps : CachedThreePhaseCaps (shadow M F E initial own) retire initial fixed arithmetic perScope)
    (localBound : fixed+(arithmetic+perScope)≤scale*2^(localPower*H)) :
    let out := runRoot M F E retire initial own
    (T.frame (Here).reached).decode out.result.1=
      reduce r.prec f ell (r.host.contract hf) ∧ out.result.2=initial ∧
      out.steps≤(pathLimit s C-r.depth+1)*scale*2^((fullPrefixConstant C+localPower)*H) := by
  letI : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r) :=
    J6R24MeteredRecursion.sourceDecision sel r
  let Q := shadow M F E initial own
  have ok : ReadyOnStack (borns Q) initial := by
    change ReadyOnStack (borns (shadow M F E initial own)) initial
    rw [shadow_births_unchanged]
    exact legal
  dsimp only
  rw [same_actual_root_meter]
  exact actual_cached_physical_output_and_compressed_rate_under_three_phase_caps Q retire initial ok
    (leaves_same_for_actual_ledger M F E initial own leaves) fit stable zero anchorPrec link
    fixed arithmetic perScope scale localPower caps localBound

#print axioms local_schedule_reads_exact_active_preparation
#print axioms actual_scope_keeps_original_own_fee
#print axioms active_local_ledger_uses_the_live_meter
#print axioms leaves_same_for_actual_ledger
#print axioms same_real_run_exact_output_and_occurrence_bill
#print axioms actual_run_r56_caps
end
end J6R66Active

