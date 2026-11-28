import A1R43LiteralDecode
import A1R43LiteralPlan
import A1R43LiteralOrigin
import A1R43LiteralBank

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8500000
set_option maxRecDepth 2500

/-! The original published A1 family with an actual zero-containing
eligible probe bank. This theorem chooses a certified layout, the real
field/word tape, and a literal active root, not any answer register.
The author's alternative nonzero-only bank is certified separately. -/
namespace A1R43Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R11Repack J6R12Repack J6R12Blueprint
open J6ActiveRun J1PPrinted J6R9Recursive
noncomputable section
attribute [local irreducible] A1R43Literal.starRoot
attribute [local irreducible] J6R12Blueprint.printedParams

variable {V : Type} [Fintype V] [DecidableEq V]
variable (F : Finset (V×V))
local notation "m" => Nat.card (Occ F)
local notation "s" => starSize m
local notation "WPlan" => PairPlan F (smallA m) (copies m)

theorem printed_A1_true_named_slot (hm : 0<m)
    (cubic : ∀ v,GraphCutMoments.degree F v=3)
    (large : (2*epsDen)^30*(1:ℕ)^10≤Nat.clog 2 s) :
    ∃ (f : ℤ[X]) (W : WPlan) (guard : PrintedMargins m)
      (cfg : RootBounds s 1 f) (hf : f.Monic) (field : Irreducible (NativeProbeRing.residuePoly f))
      (bank : EligibleBank f (J9PrintedSchedule.degreeBound (starRoot F W f).edges (2^nativeA m))),
      letI : Fact (Irreducible (NativeProbeRing.residuePoly f)) := ⟨field⟩
      let S := printedParams (f:=f) (ell:=1) s
      let d := actualStarReady F W f guard cubic cfg
      let sel := starSelector F W f guard
      let root := starRoot F W f
      let t := negativeCenter F W f guard
      let p := @J6ActiveRun.registerPrecision (J6R11Blueprint.PhysicalHost f 1) Unit S root t
      t.val=(-1:ℤ) ∧
      root.depth=0 ∧ root.prec=Fintype.card V+1 ∧
      half m≤root.edges ∧ root.edges≤s ∧
      varianceScore (declaredCell (network F (Spare F W)) (fullPacking F W).rowLabel
        (fullPacking F W).colLabel)=0 ∧
      boxNatural f 1 p hf (@J6R14ZeroMode.zeroRuntime f 1 s sel root d t hf
        (J6ActiveInterpolation.scalarIn p f 1 (NativeProbeRing.probe p f (bank.word 0))))=independentCount F ∧
      root.host.contract hf=((2^(Fintype.card V):ℕ):IntRing f 1) := by
  obtain ⟨f,W,guard,cfg,hf,hfield,hbank,_⟩ := original_A1_input_and_bank F hm cubic large
  obtain ⟨bank⟩ := hbank
  letI : Fact (Irreducible (NativeProbeRing.residuePoly f)) := ⟨hfield⟩
  have hF := J6R12Bounds.positive_degree cfg
  refine ⟨f,W,guard,cfg,hf,hfield,bank,rfl,(by unfold starRoot; rfl),(by unfold starRoot; rfl),?_,?_,full_collision_zero F W,?_,?_⟩
  · rw [root_wire_count F W f guard]
    exact guard.wire_window.1
  · rw [root_wire_count F W f guard]
    exact guard.wire_window.2
  · rw [bank.first_zero]
    exact A1_prescribed_root_exact_integer F W f guard cubic cfg hf hF
  · unfold starRoot J6R11Blueprint.PhysicalHost.contract
    letI : Fintype (Spare F W) := starFillFinite F W
    exact original_star_count F f (Fintype.card V+1) (by omega) hf hF
      (fun v=>by rw [cubic]; decide)

#print axioms printed_A1_true_named_slot
end
end A1R43Literal
