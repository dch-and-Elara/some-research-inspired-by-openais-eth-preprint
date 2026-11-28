import J6R58ActivePrepRuntime

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 19500000
set_option maxRecDepth 1700
set_option linter.unusedSectionVars false
set_option Elab.async false

/-! Apply the original same-run three-phase lemma to the machine that
actually scans the mounted words. The old mask-fee premise disappears.
Non-mask base preparation and mode-weight production retain their own
explicit tariffs. -/
namespace J6R58ActivePrep
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R56PrintedExponent J6R57ActiveFee
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R51Online J6R55CachedLedger
open J6R53PeakAddon J6R48DFS

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q n : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {fit : n≤2^f.natDegree}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (Plan sel)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)
local notation "Job" => (PageJob f ell key prec tw bw page)
local notation "Pg" => (PageBank f ell key prec tw bw page)

theorem same_leaf_meter (M : Machine) (B : MaskTable f.natDegree n fit)
    (covers : ChartCovers sel r n) (initial : Pg)
    (p : Path sel r c) (stop : c.edges≤(S).cutoff) :
    readLeaf (withActiveChart M B covers) initial p stop=readLeaf M initial p stop := by
  cases p with
  | root => rfl
  | step p w =>
    change M.leafAfter p w (sourceState (withActiveChart M B covers) p w) stop
      (stackBank (borns (withActiveChart M B covers)) initial (.step p w)) =
      M.leafAfter p w (sourceState M p w) stop (stackBank (borns M) initial (.step p w))
    rw [same_source_state,same_cached_births]

theorem same_addon_meter (M : Machine) (B : MaskTable f.natDegree n fit)
    (covers : ChartCovers sel r n) (p : Path sel r c) (child : (P).Slot c) :
    installedAddonDebit (withActiveChart M B covers) p child=installedAddonDebit M p child := by
  cases p with
  | root => rfl
  | step p w =>
    change paidAcquisition (M.demand (sourceState (withActiveChart M B covers) p w) child)=
      paidAcquisition (M.demand (sourceState M p w) child)
    rw [same_source_state]

theorem same_scope_price (M : Machine) (B : MaskTable f.natDegree n fit)
    (covers : ChartCovers sel r n) (retire : Job→ℕ) (initial : Pg)
    (p : Path sel r c) (w : (P).Slot c) :
    cachedScopeOwn (withActiveChart M B covers) retire initial p w=cachedScopeOwn M retire initial p w := by
  unfold cachedScopeOwn
  rw [same_cached_births,same_addon_meter]

theorem mounted_probe_three_phase_caps
    (M : Machine) (B : MaskTable f.natDegree n fit)
    (covers : ChartCovers sel r n) (retire : Job→ℕ) (initial : Pg)
    (K seed tape setup fixed scope : ℕ)
    (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=q) (r:=r) K)
    (cs : PrintedCentreScale s C K) (mount : ActualMountWidths M K seed)
    (fixedFits : activeNodeFixedPrice K tape (K*(3*K+5)) (setup+chartMountFee) ≤ fixed)
    (high : ∀ (z : Sigma (Path sel r)) (a : (S).cutoff<z.1.edges),
      z.1.prec+(preparedActive M z.2 a).result.extraPrecision ≤ K)
    (tapes : ∀ (z : Sigma (Path sel r)) (a : (S).cutoff<z.1.edges) t,
      ((preparedActive M z.2 a).result.tape t).tape.steps ≤ tape)
    (prep : ∀ (z : Sigma (Path sel r)) (a : (S).cutoff<z.1.edges),
      (preparedActive M z.2 a).steps ≤ setup)
    (leaf : ∀ (z : Sigma (Path sel r)) (stop : z.1.edges≤(S).cutoff),
      (readLeaf M initial z.2 stop).steps ≤ fixed)
    (visits : ∀ (z : Sigma (Path sel r)) (w : (P).Slot z.1),
      cachedScopeOwn M retire initial z.2 w ≤ scope) :
    CachedThreePhaseCaps (installActiveChart M B covers).result retire initial
      fixed (physicalAddressUnit K) scope := by
  rw [install_active_chart_exact]
  change CachedThreePhaseCaps (withActiveChart M B covers) retire initial fixed (physicalAddressUnit K) scope
  apply physical_active_bound_usable_in_r56 (withActiveChart M B covers) retire initial
    K seed tape (K*(3*K+5)) (setup+chartMountFee) fixed scope ws cs
    (same_mounted_widths M B covers mount) fixedFits
  · intro z a
    rw [exact_prepared_active]
    exact high z a
  · intro z a t
    rw [exact_prepared_active]
    exact tapes z a t
  · intro z a t i
    exact actual_installed_mask_fee M B covers z.2 a K cs ws t i
  · intro z a
    rw [exact_prepared_active]
    exact Nat.add_le_add_right (prep z a) _
  · intro z stop
    rw [same_leaf_meter]
    exact leaf z stop
  · intro z w
    rw [same_scope_price]
    exact visits z w

#print axioms same_leaf_meter
#print axioms same_addon_meter
#print axioms same_scope_price
#print axioms mounted_probe_three_phase_caps
end
end J6R58ActivePrep

