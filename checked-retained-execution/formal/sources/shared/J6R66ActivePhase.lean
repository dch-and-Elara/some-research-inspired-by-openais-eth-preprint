import J6R66ActiveLedger

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 18000000
set_option maxRecDepth 4000
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! State R56's three envelopes directly on the three actual phases of
the new runner, without giving the caller a synthetic tariff table or
making it mention the old comparison ABI. -/
namespace J6R66Active
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6R64Active J6R62ActivePrep
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Repack J6R34ChildPath J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R24MeteredRecursion J6R30ProducedGateRegistry J6R26DescriptorTree
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R49Cost J6R51Online J6R52CacheWhole J6R52Peak
open J6R55CachedLedger J6R56PrintedExponent J6R51

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

theorem original_leaf_fee_is_unchanged
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (B : L) (own : OwnsHeader E.header B)
    (p : Path sel r c) (stop : c.edges≤(S).cutoff) :
    (readLeaf (shadow M F E B own) B p stop).steps=(readLeaf M B p stop).steps := by
  let Q := shadow M F E B own
  cases p with
  | root => rfl
  | step p w =>
    change (M.leafAfter p w (sourceState Q p w) stop (stackBank (borns Q) B (.step p w))).steps=
      (M.leafAfter p w (sourceState M p w) stop (stackBank (borns M) B (.step p w))).steps
    rw [shadow_stored_sites_unchanged,shadow_births_unchanged]

theorem original_cache_mount_fee_is_unchanged
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (B : L) (own : OwnsHeader E.header B)
    (p : Path sel r c) :
    cacheMountFee (shadow M F E B own) p=cacheMountFee M p := by
  let Q := shadow M F E B own
  cases p with
  | root => rfl
  | step p w =>
    change (mountResident (sourceState Q p w) (installResidentBank (sourceState Q p w)).result).steps=
      (mountResident (sourceState M p w) (installResidentBank (sourceState M p w)).result).steps
    rw [shadow_stored_sites_unchanged]

structure LiveCaps (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (retire : J→ℕ)
    (initial : L) (own : OwnsHeader E.header initial) (fixed arithmetic perScope : ℕ) : Prop where
  leaf : ∀ (z : Sigma (Path sel r)) (stop : z.1.edges≤(S).cutoff),
    (readLeaf M initial z.2 stop).steps≤fixed
  active : ∀ (z : Sigma (Path sel r)) (a : (S).cutoff<z.1.edges),
    let A := liveActiveAt M F E initial own z.2 a
    cacheMountFee M z.2+A.steps+streamActiveTariff A.result (reachable_positive T z.2.reached) T.vPositive≤
      fixed+arithmetic*Nat.card ((P).Slot z.1)
  scope : ∀ (z : Sigma (Path sel r)) (w : (P).Slot z.1),
    cachedScopeOwn M retire initial z.2 w≤perScope

theorem live_caps_are_r56_caps_for_this_run
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (retire : J→ℕ)
    (initial : L) (own : OwnsHeader E.header initial) (fixed arithmetic perScope : ℕ)
    (G : LiveCaps M F E retire initial own fixed arithmetic perScope) :
    CachedThreePhaseCaps (shadow M F E initial own) retire initial fixed arithmetic perScope := by
  constructor
  · intro z stop
    rw [original_leaf_fee_is_unchanged]
    exact G.leaf z stop
  · intro z a
    dsimp only
    rw [local_schedule_reads_exact_active_preparation,original_cache_mount_fee_is_unchanged]
    exact G.active z a
  · intro z w
    rw [actual_scope_keeps_original_own_fee]
    exact G.scope z w

variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem same_actual_run_output_and_rate_under_live_phase_caps
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (retire : J→ℕ)
    (initial : L) (own : OwnsHeader E.header initial) (legal : ReadyOnStack (borns M) initial)
    (leaves : letI : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r) :=
      J6R24MeteredRecursion.sourceDecision sel r; LeafAgreement M initial)
    (fit : r.depth≤pathLimit s C) {anchor : Call (PhysicalHost f ell)}
    (stable : Stable s C anchor) (zero : anchor.depth=0) (anchorPrec : anchor.prec≤C*s)
    (link : NativeReach (Plan sel) anchor r)
    (fixed arithmetic perScope scale localPower : ℕ)
    (caps : LiveCaps M F E retire initial own fixed arithmetic perScope)
    (localBound : fixed+(arithmetic+perScope)≤scale*2^(localPower*H)) :
    let out := runRoot M F E retire initial own
    (T.frame (Here).reached).decode out.result.1=
      reduce r.prec f ell (r.host.contract hf) ∧ out.result.2=initial ∧
      out.steps≤(pathLimit s C-r.depth+1)*scale*2^((fullPrefixConstant C+localPower)*H) :=
  actual_run_r56_caps M F E retire initial own legal leaves fit stable zero anchorPrec link
    fixed arithmetic perScope scale localPower
    (live_caps_are_r56_caps_for_this_run M F E retire initial own fixed arithmetic perScope caps) localBound

#print axioms original_leaf_fee_is_unchanged
#print axioms original_cache_mount_fee_is_unchanged
#print axioms live_caps_are_r56_caps_for_this_run
#print axioms same_actual_run_output_and_rate_under_live_phase_caps
end
end J6R66Active

