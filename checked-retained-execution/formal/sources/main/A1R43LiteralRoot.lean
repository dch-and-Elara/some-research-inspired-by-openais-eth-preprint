import A1R43LiteralRegister
import A1R43LiteralAdmission
import A1R43LiteralFixedState
import J6R14ZeroModeFallback
import J6R12Bounds

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000
set_option maxRecDepth 2500

/-! A1 source fidelity: actual active root, legal graph-only layout,
zero-mode recursion at the fixed (-1,0,0) address, and exact integer
lifting. The same zero-mode table interpolates when zero is omitted.
No count-oracle result or complexity lower bound is an input. -/
namespace A1R43Literal
open scoped Classical BigOperators Polynomial
open Polynomial J6R10Repack J6R10Integral J6R11Integral J6R11Repack J6R12Repack J6R12Blueprint
open J6ActiveRun J6ActiveSchedule J1PPrinted J6R9Recursive
noncomputable section
attribute [local irreducible] A1R43Literal.starRoot
attribute [local irreducible] J6R12Blueprint.printedParams

variable {V : Type} [Fintype V] [DecidableEq V]
variable (F : Finset (V×V))
local notation "m" => Nat.card (Occ F)
local notation "s" => starSize m
variable (W : PairPlan F (smallA (Nat.card (Occ F))) (copies (Nat.card (Occ F))))
local notation "Pad" => Spare F W
local notation "RHost" => network F Pad
variable (f : ℤ[X])
local notation "S" => printedParams (f:=f) (ell:=1) s
local notation "Δ" => sourceDelta s
local notation "root" => starRoot F W f

theorem lift_zero_binary_probe (p : ℕ) :
    J6ActiveInterpolation.scalarIn p f 1 (NativeProbeRing.probe p f (fun _=>false))=0 := by
  rw [J6R14ZeroMode.actual_probe_zero,map_zero]

def actualStarReady (guard : PrintedMargins m) (cubic : ∀ v,GraphCutMoments.degree F v=3)
    (cfg : RootBounds s 1 f) :=
  star_ready F W f guard cubic cfg.coefficient cfg.size

theorem native_star_state_count (guard : PrintedMargins m)
    (cubic : ∀ v,GraphCutMoments.degree F v=3)
    (cfg : RootBounds s 1 f) (hf : f.Monic) (hF : 0<f.natDegree) :
    let d := actualStarReady F W f guard cubic cfg
    let t := negativeCenter F W f guard
    let p := @J6ActiveRun.registerPrecision (J6R11Blueprint.PhysicalHost f 1) Unit S root t
    (@J6R14ZeroMode.physicalZeroP f 1 s (starSelector F W f guard) root d t hf).eval 0 =
      (independentCount F:Box f 1 p) := by
  intro d t p
  exact chosen_source_star_polynomial F W f guard cubic d p
    (@J6R12Blueprint.register_positive f 1 S Δ root d t) hf hF

theorem actual_star_zero_runtime (guard : PrintedMargins m)
    (cubic : ∀ v,GraphCutMoments.degree F v=3)
    (cfg : RootBounds s 1 f)
    (hf : f.Monic) (hF : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    let d := actualStarReady F W f guard cubic cfg
    let t := negativeCenter F W f guard
    let p := registerPrecision S root t
    @J6R14ZeroMode.zeroRuntime f 1 s (starSelector F W f guard) root d t hf 0 =
      (independentCount F:Box f 1 p) := by
  intro d t p
  have hr := @J6R14ZeroMode.physicalZeroP_eval f 1 s 1 (starSelector F W f guard) root d t cfg
    (star_stable F W f guard cubic) hf hF inferInstance 0
  exact hr.symm.trans (native_star_state_count F W f guard cubic cfg hf hF)

#print axioms lift_zero_binary_probe
#print axioms native_star_state_count
#print axioms actual_star_zero_runtime
end
end A1R43Literal
