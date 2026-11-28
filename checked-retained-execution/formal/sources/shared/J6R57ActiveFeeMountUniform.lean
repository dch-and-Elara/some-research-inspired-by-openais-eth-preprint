import J6R57ActiveFeeMount
import J6R57ActiveFeeGeometry

/-! The real active mount tariff is bounded by one polynomial in
the physical row and address widths. Root has no mount; for descendants
the body bound propagates from only the actual boot's bodies. -/
namespace J6R57ActiveFee
open scoped Polynomial
open Polynomial AOracleMachineTime
open J1PPrinted J6ActiveRun J6R10Repack J6R10Reachable J6R11Blueprint J6R12Blueprint J6R16ModeCost
open J6R24MeteredRecursion J6R26DescriptorTree J6R36ChildFramedRoute
open J6R50SourceProducer J6R51Online J6R51Peak J6R52Peak J6R55CachedLedger
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 14000000
set_option maxRecDepth 3400
set_option linter.unusedSectionVars false
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}

structure ActualMountWidths (M : OnlineMachine T key prec tw bw page q) (K seed : ℕ) : Prop where
  edges : C*s ≤ K
  labelLanes : Nat.clog 2 s ≤ K
  keyBits : key ≤ K
  precisionWord : prec ≤ K
  pageBits : page ≤ K
  bodyBits : sourceBodyCap s C seed ≤ K
  portBits : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (Plan sel).Slot x),
    (sourceState M p w).birth.port ≤ K
  ownerBits : ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (Plan sel).Slot x),
    (sourceState M p w).site.ownerWidth ≤ K
  bootBodies : ∀ (w : (Plan sel).Slot r) h,
    ((M.initial w).result.birth.native.physical.record h).body.length ≤ seed

theorem actual_mount_caps_from_physical_words (M : OnlineMachine T key prec tw bw page q)
    (K seed : ℕ) (within : ActualMountWidths M K seed) (p : Path sel r c) :
    cacheMountFee M p ≤ 256*(K+1)^3 := by
  cases p with
  | root => exact Nat.zero_le _
  | step p w =>
    have base := actual_descendant_cache_cap_from_boot M seed within.bootBodies p w
    have n0 := (physical_edges_at_most_root_scale (cfg:=cfg) p T.rootStable).trans within.edges
    have n1 := (physical_edges_at_most_root_scale (cfg:=cfg) (Path.step p w) T.rootStable).trans within.edges
    have a : J6R36ChildFramedRoute.dim (p.ticket w) ≤ K :=
      (bits_le_lam (Nat.clog 2 s) _).trans within.labelLanes
    exact base.trans (frameMountCap_polynomial n0 n1 (within.portBits p w) (within.ownerBits p w)
      a within.keyBits within.precisionWord within.pageBits within.bodyBits)

#print axioms ActualMountWidths
#print axioms actual_mount_caps_from_physical_words
end
end J6R57ActiveFee
