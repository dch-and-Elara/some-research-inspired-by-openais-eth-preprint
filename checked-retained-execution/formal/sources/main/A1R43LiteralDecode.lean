import A1R43LiteralRoot

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000
set_option maxRecDepth 2000

/-! Exact integer readout of the same actual named zero-mode runtime.
The length of a binary original table and the root precision are not
read from the number of packet copies. -/
namespace A1R43Literal
open scoped Polynomial
open Polynomial J6R9Recursive J6R12Repack J6R12Blueprint J6ActiveRun J6ActiveSchedule J1PPrinted
noncomputable section
attribute [local irreducible] A1R43Literal.starRoot
attribute [local irreducible] J6R12Blueprint.printedParams

variable {V : Type} [Fintype V] [DecidableEq V]
variable (F : Finset (V×V))
local notation "m" => Nat.card (Occ F)
local notation "s" => starSize m
variable (W : PairPlan F (smallA (Nat.card (Occ F))) (copies (Nat.card (Occ F))))
variable (f : ℤ[X])
local notation "S" => printedParams (f:=f) (ell:=1) s
local notation "r" => starRoot F W f
local notation "Δ" => sourceDelta s

theorem above_vertex_precision (guard : PrintedMargins m)
    (d : @J6R12Blueprint.Ready f 1 S Δ r) :
    Fintype.card V < registerPrecision S r (negativeCenter F W f guard) := by
  have hM : 0<(r).edges := (Nat.zero_le _).trans_lt (@J6R12Blueprint.Ready.active f 1 S Δ r d)
  have h := child_monotone (r).prec ((S).levelBits (r).depth) (r).edges ((S).levelWidth (r).depth)
    (negativeCenter F W f guard).val hM
  have h0 : (r).prec=Fintype.card V+1 := by unfold starRoot; rfl
  calc
    Fintype.card V < Fintype.card V+1 := Nat.lt_succ_self _
    _ < registerPrecision S r (negativeCenter F W f guard) := by
      unfold registerPrecision
      simpa only [h0] using h

theorem A1_prescribed_root_exact_integer (guard : PrintedMargins m)
    (cubic : ∀ v,GraphCutMoments.degree F v=3) (cfg : RootBounds s 1 f)
    (hf : f.Monic) (hF : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    let d := actualStarReady F W f guard cubic cfg
    let t := negativeCenter F W f guard
    let p := @J6ActiveRun.registerPrecision (J6R11Blueprint.PhysicalHost f 1) Unit S r t
    boxNatural f 1 p hf (@J6R14ZeroMode.zeroRuntime f 1 s (starSelector F W f guard) r d t hf
      (J6ActiveInterpolation.scalarIn p f 1 (NativeProbeRing.probe p f (fun _=>false)))) =
      independentCount F := by
  intro d t p
  let v : Box f 1 p→Box f 1 p :=
    @J6R14ZeroMode.zeroRuntime f 1 s (starSelector F W f guard) r d t hf
  have hzero := congrArg v (lift_zero_binary_probe f p)
  have hv : v 0 = (independentCount F:Box f 1 p) :=
    actual_star_zero_runtime F W f guard cubic cfg hf hF
  have hp := @J6R12Blueprint.register_positive f 1 S Δ r d t
  have hN := above_vertex_precision F W f guard d
  have hfit := (independentCount_le F).trans_lt (Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) hN)
  have hx := boxNatural_of_nat f 1 p hf hp (by decide) hF (independentCount F) hfit
  exact (congrArg (boxNatural f 1 p hf) (hzero.trans hv)).trans hx

theorem same_slot_if_zero_omitted (guard : PrintedMargins m)
    (cubic : ∀ v,GraphCutMoments.degree F v=3) (cfg : RootBounds s 1 f)
    (hf : f.Monic) (hF : 0<f.natDegree)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (bank : J6R14ZeroMode.Prescribed f
      (J9PrintedSchedule.degreeBound (r).edges (2^((S).levelBits (r).depth)))) :
    let d := actualStarReady F W f guard cubic cfg
    let t := negativeCenter F W f guard
    let p := @J6ActiveRun.registerPrecision (J6R11Blueprint.PhysicalHost f 1) Unit S r t
    boxNatural f 1 p hf (@J6R14ZeroMode.fallback f 1 s (starSelector F W f guard) r d t hf bank)=
      independentCount F := by
  intro d t p
  have hfall := @J6R14ZeroMode.fallback_exact f 1 s 1 (starSelector F W f guard) r d t cfg
    (star_stable F W f guard cubic) hf hF inferInstance bank
  have hactual := actual_star_zero_runtime F W f guard cubic cfg hf hF
  have hFst := congrArg (boxNatural f 1 p hf) (hfall.trans hactual)
  have hp := @J6R12Blueprint.register_positive f 1 S Δ r d t
  have hN := above_vertex_precision F W f guard d
  have hfit := (independentCount_le F).trans_lt (Nat.pow_lt_pow_right (by decide : 1<(2:ℕ)) hN)
  exact hFst.trans (boxNatural_of_nat f 1 p hf hp (by decide) hF (independentCount F) hfit)

#print axioms above_vertex_precision
#print axioms A1_prescribed_root_exact_integer
#print axioms same_slot_if_zero_omitted
end
end A1R43Literal
