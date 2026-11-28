import J6R68AbsolutePrescribedMenu
import J6R66ActivePhase
import J6R56PrintedExponentPhases

/-! Same physical R66 run and fee ledger, with the exact initialized
absolute source invariant replacing the unneeded claimed native
anchor-to-exterior transition. Local producer caps are still explicit. -/
namespace J6R68AbsolutePrescribed
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R49Cost
open J6R51Online J6R52CacheWhole J6R52Peak J6R53PeakAddon J6R54PeakInput
open J6R55CachedLedger J6R56PrintedExponent J6R66Active J6R64Active J6R51

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4700
set_option maxHeartbeats 35000000
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (Plan sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "Mchn" => (OnlineMachine T key prec tw bw page q)
local notation "Q" => (nativeScopedPlan sel r)
local notation "Here" => (Path.root : Path sel r r)
local notation "root" => (Sigma.mk r Here)
local notation "lam" => (Nat.clog 2 s)
local notation "H" => (J9PrintedSchedule.leafThreshold s lam)

include cfg in
theorem actual_scoped_fanout_from_prescribed (seed : AbsoluteSeed s C r)
    (j : ℕ) (z : Sigma (Path sel r)) (seen : z∈occurrences Q root j) :
    Nat.card ((Q).Slot z)≤2^(branchBits lam+depthExponent s C lam (siteConstant C) j) := by
  have absDep : z.1.depth=r.depth+j :=
    (occurrence_reach_depth Q (fun x=>x.1.depth) (fun _ _=>rfl) root j z seen).2
  exact (actual_suffix_addresses_from_prescribed_seed cfg sel seed z.2).trans
    (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left
      (depth_exponent_antitone s C lam (siteConstant C) (show j≤z.1.depth by omega)) _))

variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem physical_run_compressed_from_prescribed_seed
    (M : Mchn) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (retire : J→ℕ)
    (initial : L) (own : OwnsHeader E.header initial) (legal : ReadyOnStack (borns M) initial)
    (leaves : letI : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r) :=
      J6R24MeteredRecursion.sourceDecision sel r; LeafAgreement M initial)
    (seed : AbsoluteSeed s C r)
    (fixed arithmetic perScope scale localPower : ℕ)
    (caps : LiveCaps M F E retire initial own fixed arithmetic perScope)
    (localBound : fixed+(arithmetic+perScope)≤scale*2^(localPower*H)) :
    let out := J6R66Active.runRoot M F E retire initial own
    (T.frame (Here).reached).decode out.result.1=
      reduce r.prec f ell (r.host.contract hf) ∧ out.result.2=initial ∧
      out.steps≤(pathLimit s C-r.depth+1)*scale*2^((fullPrefixConstant C+localPower)*H) := by
  let source := shadow M F E initial own
  let out := J6R66Active.runRoot M F E retire initial own
  obtain ⟨value,restored,bill⟩ :=
    same_real_run_exact_output_and_occurrence_bill M F E retire initial own legal leaves seed.depth
  refine ⟨value,restored,?_⟩
  let addresses := arithmetic+perScope
  have primitive := live_caps_are_r56_caps_for_this_run M F E retire initial own fixed arithmetic perScope caps
  have affine := actual_cached_affine_from_phase_caps source retire initial fixed arithmetic perScope primitive
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

#print axioms actual_scoped_fanout_from_prescribed
#print axioms physical_run_compressed_from_prescribed_seed
end
end J6R68AbsolutePrescribed
