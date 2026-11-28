import A1R43LiteralPaidRoot
import V8NativeMessageN2DLabelsPlanFormat

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7500000
set_option maxRecDepth 2200

/-! The same actual tape-selected A1 example from finite graph orders.
No manually supplied endpoint/label encoder is required. Obtaining and
writing these orders from an external file is still not metered. -/
namespace A1R43Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6R9Recursive J6R12Blueprint J6ActiveRun J1PPrinted J6R12Repack
open J6R12CollisionGreedyStep J6R12CollisionSource J6R12CollisionMenu
open V8NativeMessage.N2DLabels J6R14LayoutCost
noncomputable section
attribute [local irreducible] A1R43Literal.starRoot
attribute [local irreducible] J6R12Blueprint.printedParams

variable {V : Type} [Fintype V] [DecidableEq V]
variable (F : Finset (V×V))
local notation "m" => Nat.card (Occ F)
local notation "s" => starSize m
local notation "a" => smallA m
local notation "WPlan" => PairPlan F a (copies m)
variable (O : GraphOrders (Occ F) F V)

theorem actual_orders_feed_named_count
    (guard : PrintedMargins m) (cubic : ∀ v,GraphCutMoments.degree F v=3)
    (f : ℤ[X]) (cfg : RootBounds s 1 f) (hf : f.Monic)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    let input := formatFromOrders (simulated F) a O
    let Fmt := input.format
    let out := drive Fmt.e Fmt.kR Fmt.kC Fmt.b (input.order.map Fmt.target) (Fmt.graph (fun _=>none))
    ∃ (z : ↥F⊕V→Fin a→Fin 64) (W : WPlan),
      W.row=(fun r=>z (.inl r)) ∧ W.col=(fun c=>z (.inr c)) ∧
      out.result.1=Fmt.graph (fun i=>some (z i)) ∧
      out.result.2=input.order.map (fun i=>coordinateLabel (z i)) ∧
      out.steps≤(Fmt.stepBound (2^(6*a))+2*Fmt.b+6)*(Fintype.card (↥F)+Fintype.card V) +
        16*(Fmt.b+1)*2^(6*a)+12*Fmt.width+20 ∧
      let S := printedParams (f:=f) (ell:=1) s
      let root := starRoot F W f
      let t := negativeCenter F W f guard
      let p := @J6ActiveRun.registerPrecision (J6R11Blueprint.PhysicalHost f 1) Unit S root t
      let d := actualStarReady F W f guard cubic cfg
      boxNatural f 1 p hf (@J6R14ZeroMode.zeroRuntime f 1 s (starSelector F W f guard) root d t hf
        (J6ActiveInterpolation.scalarIn p f 1 (NativeProbeRing.probe p f (fun _=>false)))) =
        independentCount F := by
  let input := formatFromOrders (simulated F) a O
  obtain ⟨z,W,hR,hC,hG,hW,hFee,hCount⟩ := same_paid_labels_same_named_count F guard cubic
    input.format input.rowExact input.colExact input.labelWidth input.order input.distinct input.complete
    f cfg hf
  refine ⟨z,W,hR,hC,hG,hW.trans ?_,hFee,hCount⟩
  apply List.map_congr_left
  intro x _
  exact format_coordinates (simulated F) a O (z x)

#print axioms actual_orders_feed_named_count
end
end A1R43Literal
