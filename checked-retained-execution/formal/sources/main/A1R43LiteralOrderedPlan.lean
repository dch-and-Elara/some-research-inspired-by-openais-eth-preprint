import A1R43LiteralOrders
import A1R43LiteralPlan

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9500000
set_option maxRecDepth 2300

/-! One selected hard input: the supplied graph ordinals feed the actual
metered label generation, and the exact first probe of the legal source
bank queries that very same installed layout. -/
namespace A1R43Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6R9Recursive J6R12Blueprint J6ActiveRun J1PPrinted J6R12Repack
open J6R12CollisionGreedyStep J6R12CollisionSource J6R14LayoutCost
open V8NativeMessage.N2DLabels
noncomputable section
attribute [local irreducible] A1R43Literal.starRoot
attribute [local irreducible] J6R12Blueprint.printedParams

variable {V : Type} [Fintype V] [DecidableEq V]
variable (F : Finset (V×V))
local notation "m" => Nat.card (Occ F)
local notation "s" => starSize m
local notation "a" => smallA m
local notation "WPlan" => PairPlan F a (copies m)

theorem printed_same_paid_graph_named_integer (O : GraphOrders (Occ F) F V)
    (hm : 0<m) (cubic : ∀ v,GraphCutMoments.degree F v=3)
    (large : (2*epsDen)^30*(1:ℕ)^10≤Nat.clog 2 s) :
    let input := formatFromOrders (simulated F) a O
    let Fmt := input.format
    let out := drive Fmt.e Fmt.kR Fmt.kC Fmt.b (input.order.map Fmt.target) (Fmt.graph (fun _=>none))
    ∃ (f : ℤ[X]) (guard : PrintedMargins m) (cfg : RootBounds s 1 f)
      (hf : f.Monic) (field : Irreducible (NativeProbeRing.residuePoly f))
      (z : ↥F⊕V→Fin a→Fin 64) (W : WPlan)
      (bank : EligibleBank f (J9PrintedSchedule.degreeBound (starRoot F W f).edges (2^nativeA m))),
      letI : Fact (Irreducible (NativeProbeRing.residuePoly f)) := ⟨field⟩
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
        (J6ActiveInterpolation.scalarIn p f 1 (NativeProbeRing.probe p f (bank.word 0)))) =
        independentCount F := by
  obtain ⟨f,cfg,hf,hfield,words,hfirst,hwords⟩ := J6R12Bounds.sourceField_of_printed_guard s 1
    (by decide) large
  let guard := printed_margins m hm cfg.widthPos
  letI : Fact (Irreducible (NativeProbeRing.residuePoly f)) := ⟨hfield⟩
  obtain ⟨z,W,hRow,hCol,hGraph,hWords,hFee,hCount⟩ :=
    actual_orders_feed_named_count F O guard cubic f cfg hf
  obtain ⟨bank⟩ := eligible_probe_bank_on_star F W guard cubic f cfg words hfirst
    (fun p hp=>(hwords p hp).2)
  refine ⟨f,guard,cfg,hf,hfield,z,W,bank,hRow,hCol,hGraph,hWords,hFee,?_⟩
  rw [bank.first_zero]
  exact hCount

#print axioms printed_same_paid_graph_named_integer
end
end A1R43Literal
