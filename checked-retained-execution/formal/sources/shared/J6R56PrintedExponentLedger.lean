import J6R56PrintedExponent
import J6R55CachedLedgerRoot
import J6R11BlueprintAdapter

/-! Apply the printed exponent bound to the exact cached occurrence
ledger. An exterior run can start at nonzero absolute depth, but its
printed fan-out certificate must come from the same depth-zero chart. -/
namespace J6R56PrintedExponent
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R49Cost
open J6R51Online J6R52CacheWhole J6R52Peak J6R53PeakAddon J6R54PeakInput
open J6R55CachedLedger

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3900
set_option maxHeartbeats 26000000
set_option linter.unusedSectionVars false
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "Q" => (nativeScopedPlan sel r)
local notation "root" => (Sigma.mk r (Path.root : Path sel r r))
local notation "lam" => (Nat.clog 2 s)
local notation "H" => (J9PrintedSchedule.leafThreshold s lam)

theorem depth_exponent_antitone (s C l K : ℕ) : Antitone (depthExponent s C l K) := by
  intro a b hab
  unfold depthExponent
  apply Nat.mul_le_mul_left
  exact Nat.div_le_div_left (Nat.pow_le_pow_right (by decide : 0<(4:ℕ)) hab)
    (Nat.pow_pos (by decide))

theorem actual_scoped_fanout_from_anchor (cfg : RootBounds s C f)
    {anchor : Call (PhysicalHost f ell)}
    (stable : Stable s C anchor) (zero : anchor.depth=0) (anchorPrec : anchor.prec≤C*s)
    (link : NativeReach (Plan sel) anchor r)
    (j : ℕ) (z : Sigma (Path sel r)) (seen : z∈occurrences Q root j) :
    Nat.card ((Q).Slot z)≤2^(branchBits lam+depthExponent s C lam (siteConstant C) j) := by
  have absReach := nativeReach_trans (Plan sel) link z.2.reached
  have absDep : z.1.depth=r.depth+j :=
    (occurrence_reach_depth Q (fun x=>x.1.depth) (fun _ _=>rfl) root j z seen).2
  exact (live_addresses_bound cfg sel absReach stable zero anchorPrec).trans
    (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left
      (depth_exponent_antitone s C lam (siteConstant C) (show j≤z.1.depth by omega)) _))

variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem actual_cached_absolute_meter_compressed
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (initial : PageBank f ell key prec tw bw page)
    (legal : ReadyOnStack (borns M) initial)
    (fit : r.depth≤pathLimit s C)
    {anchor : Call (PhysicalHost f ell)}
    (stable : Stable s C anchor) (zero : anchor.depth=0) (anchorPrec : anchor.prec≤C*s)
    (link : NativeReach (Plan sel) anchor r)
    (fixed address : ℕ)
    (phaseCap : ∀ z : Sigma (Path sel r),
      cachedOwn M retire initial z≤fixed+address*Nat.card ((Plan sel).Slot z.1)) :
    (runCachedRootSingleEmission M retire initial).steps≤
      (pathLimit s C-r.depth+1)*(fixed+address)*2^(fullPrefixConstant C*H) := by
  apply compress_absolute_meter_bound s C r.depth _ _ cfg.constPos cfg.size (root_lambda_large cfg)
  apply (same_single_emission_cached_ledger M retire initial legal fit).trans
  let hFan := actual_scoped_fanout_from_anchor (sel:=sel) (r:=r) cfg stable zero anchorPrec link
  exact total_fee_bound Q root s C lam (siteConstant C) (branchBits lam)
    (pathLimit s C-r.depth+1) (fixed+address) (cachedOwn M retire initial)
    hFan (fun j z seen=>local_charge_affine_le (phaseCap z) (hFan j z seen))

theorem actual_cached_source_root_meter_compressed
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (initial : PageBank f ell key prec tw bw page)
    (legal : ReadyOnStack (borns M) initial) (zero : r.depth=0) (rootPrec : r.prec≤C*s)
    (fixed address : ℕ)
    (phaseCap : ∀ z : Sigma (Path sel r),
      cachedOwn M retire initial z≤fixed+address*Nat.card ((Plan sel).Slot z.1)) :
    (runCachedRootSingleEmission M retire initial).steps≤
      (pathLimit s C+1)*(fixed+address)*2^(fullPrefixConstant C*H) := by
  have fit : r.depth≤pathLimit s C := by rw [zero]; exact Nat.zero_le _
  simpa only [zero,Nat.sub_zero] using actual_cached_absolute_meter_compressed M retire initial
    legal fit T.rootStable zero rootPrec (.reflexive r) fixed address phaseCap

#print axioms depth_exponent_antitone
#print axioms actual_scoped_fanout_from_anchor
#print axioms actual_cached_absolute_meter_compressed
#print axioms actual_cached_source_root_meter_compressed
end
end J6R56PrintedExponent
