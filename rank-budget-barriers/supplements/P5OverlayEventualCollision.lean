import P5EveryPrintedRoot

/-! The actual packing is quantified after the uniform size threshold and
before any pin input. This version uses the collision certificate itself:
the packing need not arise from the printed greedy selector. -/
namespace Paper5.D1Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R11Repack J6R11Blueprint J6R12Blueprint
  P11FullPacking Paper5.HybridClosure J1PPrinted GraphCutMoments
open Paper5.HybridClosure.Printed (dLambda printedExponent)

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 11000000
set_option maxRecDepth 3000

theorem eventual_every_collision_packing_root (γ : ℚ) (hg : 0<γ) (hg₃ : γ≤3) :
    ∃ n₀ : ℕ, ∀ (W : Type) [Fintype W] [DecidableEq W] [Nonempty W]
      (F : Finset (W × W)) (reg : ∀ v,degree F v=3) (_ : ∀ v,(v,v)∉F),
      n₀ ≤ Fintype.card W →
      (∀ U : Finset W, (γ/3)*(min U.card (Fintype.card W-U.card):ℕ)≤((boundary F U).card:ℚ)) →
      ∀ (f : ℤ[X]) (_ : f.natDegree=4*dLambda (Fintype.card W)) (hf : f.Monic)
        [Fact (Irreducible (NativeProbeRing.residuePoly f))] (P : RootPacking F reg f),
      CollisionBound F reg f P →
      ∃ d : Ready (printedParams (f:=f) (ell:=1) (oldRowSize F)) (sourceDelta (oldRowSize F))
          (oldRowRoot F reg f (fun _ => false)),
        2^(printedExponent γ (Fintype.card W)) ≤ Fintype.card (PublicSlot F reg f P d) ∧
        ∀ σ : W→Bool, 2^(printedExponent γ (Fintype.card W)) ≤
          (rootVisitLedger F reg f P d hf σ).length := by
  obtain ⟨n₀,hn⟩ := original_D1_size_threshold γ hg
  refine ⟨n₀,?_⟩
  intro W _ _ _ F reg loop hN expand f hdeg hf _ P collision
  obtain ⟨ready,size⟩ := hn _ hN
  exact every_collision_packing_visits F reg f loop γ hg hg₃ expand ready size hdeg hf P collision

#print axioms eventual_every_collision_packing_root
end Paper5.D1Literal
