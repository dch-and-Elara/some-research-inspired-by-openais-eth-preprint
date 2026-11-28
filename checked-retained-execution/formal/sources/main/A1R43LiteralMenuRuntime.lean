import V8PooledMenuSlots
import J6R14ZeroModeRun

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8500000
set_option maxRecDepth 2500

/-! The V8 completed-slot interface at zero mode is the result of executing
the same native recursive child product, not a fresh source contraction. -/
namespace A1R43Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6ActiveRun J6R9Recursive J6R11Blueprint J6R12Blueprint
open J6R12Repack J6R10Integral J6R11Integral J1PPrinted
noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams

variable {f : ℤ[X]} {ell s C : ℕ}
local notation "S" => printedParams (f:=f) (ell:=ell) s
local notation "Δ" => sourceDelta s
abbrev installedWidth (c : Call (PhysicalHost f ell))
    (t : @J6ActiveRun.Center (PhysicalHost f ell) Unit S c) :=
  @J6ActiveRun.registerPrecision (PhysicalHost f ell) Unit S c t

def namedPooledZeroSlot (sel : @Selector f ell S Δ) (c : Call (PhysicalHost f ell))
    (d : @Ready f ell S Δ c) (t : @J6ActiveRun.Center (PhysicalHost f ell) Unit S c)
    (hf : f.Monic) (z : Box f ell (@installedWidth f ell s c t)) :
    Box f ell (@installedWidth f ell s c t) := by
  letI : Fintype c.host.Edge := c.host.finiteEdge
  letI : Fintype c.host.Row := c.host.finiteRow
  letI : Fintype c.host.Col := c.host.finiteCol
  let p := @installedWidth f ell s c t
  exact V8PooledMenu.slot (f:=f) (ell:=ell) (t:=t.val) (packing sel d)
    (centerIndex d t) (centerNonzero t) rfl p (box_two_nil p f ell) z c.host.file hf 0

theorem completed_zero_slot_is_source_runtime
    (sel : @Selector f ell S Δ) (c : Call (PhysicalHost f ell))
    (d : @Ready f ell S Δ c) (t : @J6ActiveRun.Center (PhysicalHost f ell) Unit S c)
    (cfg : RootBounds s C f) (seed : Stable s C c) (hf : f.Monic) (hF : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] (z : Box f ell (@installedWidth f ell s c t)) :
    namedPooledZeroSlot sel c d t hf z =
      @J6R14ZeroMode.zeroRuntime f ell s sel c d t hf z := by
  letI := c.host.finiteEdge
  letI := c.host.finiteRow
  letI := c.host.finiteCol
  unfold namedPooledZeroSlot V8PooledMenu.slot J6R14ZeroMode.zeroRuntime
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [@J6R14ZeroMode.zeroChildRun_exact f ell s C sel c d t cfg seed hf hF inferInstance z g]
  let p := @installedWidth f ell s c t
  exact congrArg (reduce p f ell)
    (J6R12Integral.actualPacketHost_truth (packing sel d) (centerIndex d t)
      (centerNonzero t) rfl p z c.host.file hf 0 g)

#print axioms namedPooledZeroSlot
#print axioms completed_zero_slot_is_source_runtime
end
end A1R43Literal
