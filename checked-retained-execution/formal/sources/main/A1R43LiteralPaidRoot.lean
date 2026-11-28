import A1R43LiteralDecode
import A1R43LiteralPaidLayout

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9000000
set_option maxRecDepth 2500

/-! Same actual A1 root when the layout words are taken from the paid
conditional-expectation program on the original explicit simulated
graph. This does not price the entire raw-input preprocessing. -/
namespace A1R43Literal
open scoped Classical BigOperators Polynomial
open Polynomial J6R9Recursive J6R12Blueprint J6ActiveRun J1PPrinted J6R12Repack
open J6R12CollisionGreedyStep J6R12CollisionSource
noncomputable section
attribute [local irreducible] A1R43Literal.starRoot
attribute [local irreducible] J6R12Blueprint.printedParams

variable {V : Type} [Fintype V] [DecidableEq V]
variable (F : Finset (V×V))
local notation "m" => Nat.card (Occ F)
local notation "s" => starSize m
local notation "a" => smallA m
local notation "WPlan" => PairPlan F a (copies m)

theorem same_paid_labels_same_named_count
    (guard : PrintedMargins m) (cubic : ∀ v,GraphCutMoments.degree F v=3)
    (Fmt : Format (Occ F) F V (Fin a→Fin 64))
    (hr : Fmt.row=(simulated F).row) (hc : Fmt.col=(simulated F).col)
    (hb : Fmt.b=6*a) (vs : List (↥F⊕V)) (hn : vs.Nodup) (hv : ∀ i,i∈vs)
    (f : ℤ[X]) (cfg : RootBounds s 1 f) (hf : f.Monic)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))] :
    let out := drive Fmt.e Fmt.kR Fmt.kC Fmt.b (vs.map Fmt.target) (Fmt.graph (fun _=>none))
    ∃ (z : ↥F⊕V→Fin a→Fin 64) (W : WPlan),
      W.row=(fun r=>z (.inl r)) ∧ W.col=(fun c=>z (.inr c)) ∧
      out.result.1=Fmt.graph (fun i=>some (z i)) ∧
      out.result.2=vs.map (fun i=>Fmt.label (z i)) ∧
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
  dsimp only
  have hA (e : F) : Nat.card {u : Occ F//(simulated F).row u=e}≤3 := by
    rw [simulated_row_degree]; decide
  have hB (v : V) : Nat.card {u : Occ F//(simulated F).col u=v}≤3 := by
    change Nat.card {u : Occ F//endpoint F u=v}≤3
    rw [incidence_card,cubic]
  obtain ⟨z,W,hrw,hcw,hgraph,hwords,hpaid,_⟩ :=
    General.exact_chosen_labels_feed_actual_pair_plan (simulated F) m rfl rfl guard Fmt hr hc
      hb vs hn hv 3 (by decide) hA hB
  let A : WPlan := ⟨W.shared,W.row,W.col,W.capacity⟩
  have hF := J6R12Bounds.positive_degree cfg
  exact ⟨z,A,hrw,hcw,hgraph,hwords,hpaid,
    A1_prescribed_root_exact_integer F A f guard cubic cfg hf hF⟩

#print axioms same_paid_labels_same_named_count
end
end A1R43Literal
