import J6R57ActiveFeeFixed
import J6R57ActiveFeeMountUniform

/-! Replace the active-cap guard in the R56 same-run theorem by actual
source widths and opaque, separately identified producer meters. Leaf
and per-scope prices are not handled by this arithmetic module. -/
namespace J6R57ActiveFee
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R48BitCost J6R49DFS J6R49Cost J6R50Peak
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R51Online J6R55CachedLedger
open J6R56PrintedExponent

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 16000000
set_option maxRecDepth 3800
set_option linter.unusedSectionVars false
set_option Elab.async false

def activeNodeFixedPrice (K tape mask setup : ℕ) : ℕ :=
  256*(K+1)^3+setup+fixedArithmeticPx K tape mask

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}

theorem actual_high_fits_when_source_chose_canonical
    (M : OnlineMachine T key prec tw bw page q) (p : Path sel r c)
    (a : (printedParams (f:=f) (ell:=ell) s).cutoff<c.edges)
    (K : ℕ)
    (canon : (preparedActive M p a).result.extraPrecision=
      commonLoss ((printedParams (f:=f) (ell:=ell) s).levelBits c.depth) c.edges
        ((printedParams (f:=f) (ell:=ell) s).levelWidth c.depth))
    (fit : absolutePrecision s r.edges r.prec+(C*s)*(24*2^(Nat.clog 2 s)+4*(Nat.clog 2 s+1)) ≤ K) :
    c.prec+(preparedActive M p a).result.extraPrecision ≤ K := by
  obtain ⟨uPos,uFit⟩ := (J6R12Integral.printedGuards cfg sel r T.rootStable).taper _ p.reached a
  have hA : (printedParams (f:=f) (ell:=ell) s).levelBits c.depth ≤ Nat.clog 2 s :=
    J6R16ModeCost.bits_le_lam _ _
  have e := physical_edges_at_most_root_scale (cfg:=cfg) p T.rootStable
  have loss := (simple_common_scale_cap hA uPos uFit).trans (Nat.mul_le_mul_right _ e)
  have pr := absolute_inherited_precision_cap cfg sel T.rootStable p
  rw [canon]
  exact (Nat.add_le_add pr loss).trans fit

theorem actual_active_phase_polynomial_physical
    (M : OnlineMachine T key prec tw bw page q) (p : Path sel r c)
    (a : (printedParams (f:=f) (ell:=ell) s).cutoff<c.edges)
    (K seed tape mask setup : ℕ)
    (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=q) (r:=r) K)
    (cs : PrintedCentreScale s C K) (mount : ActualMountWidths M K seed)
    (high : c.prec+(preparedActive M p a).result.extraPrecision ≤ K)
    (allTapes : ∀ t,((preparedActive M p a).result.tape t).tape.steps ≤ tape)
    (allMasks : ∀ t z,(((preparedActive M p a).result.tape t).masks z).steps ≤ mask)
    (prep : (preparedActive M p a).steps ≤ setup) :
    let A := preparedActive M p a
    cacheMountFee M p+A.steps+streamActiveTariff A.result (reachable_positive T p.reached) T.vPositive ≤ activeNodeFixedPrice K tape mask setup+physicalAddressUnit K*Nat.card ((Plan sel).Slot c) :=
  actual_active_node_affine_with_paid_suppliers M p a K tape mask setup (256*(K+1)^3)
    ws cs high allTapes allMasks prep (actual_mount_caps_from_physical_words M K seed mount p)

theorem physical_active_bound_usable_in_r56
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ) (initial : PageBank f ell key prec tw bw page)
    (K seed tape mask setup fixed scope : ℕ)
    (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=q) (r:=r) K)
    (cs : PrintedCentreScale s C K) (mount : ActualMountWidths M K seed)
    (fixedFits : activeNodeFixedPrice K tape mask setup ≤ fixed)
    (high : ∀ (z : Sigma (Path sel r))
      (a : (printedParams (f:=f) (ell:=ell) s).cutoff<z.1.edges),
      z.1.prec+(preparedActive M z.2 a).result.extraPrecision ≤ K)
    (tapes : ∀ (z : Sigma (Path sel r))
      (a : (printedParams (f:=f) (ell:=ell) s).cutoff<z.1.edges) t,
      ((preparedActive M z.2 a).result.tape t).tape.steps ≤ tape)
    (masks : ∀ (z : Sigma (Path sel r))
      (a : (printedParams (f:=f) (ell:=ell) s).cutoff<z.1.edges) t i,
      (((preparedActive M z.2 a).result.tape t).masks i).steps ≤ mask)
    (prep : ∀ (z : Sigma (Path sel r))
      (a : (printedParams (f:=f) (ell:=ell) s).cutoff<z.1.edges),
      (preparedActive M z.2 a).steps ≤ setup)
    (leaf : ∀ (z : Sigma (Path sel r)) (stop : z.1.edges ≤ (printedParams (f:=f) (ell:=ell) s).cutoff),
      (readLeaf M initial z.2 stop).steps ≤ fixed)
    (visits : ∀ (z : Sigma (Path sel r)) (w : (Plan sel).Slot z.1),
      cachedScopeOwn M retire initial z.2 w ≤ scope) :
    CachedThreePhaseCaps M retire initial fixed (physicalAddressUnit K) scope := by
  refine ⟨leaf,?_,visits⟩
  intro z a
  exact (actual_active_phase_polynomial_physical M z.2 a K seed tape mask setup ws cs mount
    (high z a) (tapes z a) (masks z a) (prep z a)).trans (Nat.add_le_add_right fixedFits _)

#print axioms actual_high_fits_when_source_chose_canonical
#print axioms actual_active_phase_polynomial_physical
#print axioms physical_active_bound_usable_in_r56
end
end J6R57ActiveFee
