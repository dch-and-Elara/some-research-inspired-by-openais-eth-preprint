import V8NativeMessageN8LiteralEnd
import V8NativeMessageN8LiteralPrintedInputs

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2550000

/-! The original sufficiently-large-size N8 conclusion using the
literal four-copy size and actual printed root schedule. -/
namespace V8NativeMessage.N8Literal
open scoped Classical Polynomial
open Polynomial J6R12Blueprint J6R10Repack P11FullPacking J1PPrinted
open Paper5.HybridClosure Paper5.HybridClosure.Printed Paper5.D1Literal
open V8NativeMessage.N4 V8NativeMessage.N6D

noncomputable section

/-- At a fixed expansion constant the same original estimator fails
for all sufficiently large legal old-row instances and any fixed
retained coordinate of its common packing. -/
theorem original_N8_printed_failure (γ : ℝ) (hγ : 0<γ) :
    ∃ n₀ : ℕ, ∀ (W : Type) [Fintype W] [DecidableEq W]
      (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3) (f : ℤ[X]),
      n₀≤Fintype.card W →
      ∀ (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f)) (i : rootKept F f)
        (q : ℕ) (cap : q≤(printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0+1-i.val.val)
        (hf : f.Monic) (_hd : 0<f.natDegree),
        varianceScore (actualCell P)≤2*(Nat.card (DWire F):ℚ)*sourceDelta (oldRowSize F) →
        V8NativeMessage.C2Physical.ExpansionOn (storageGraph F) γ →
        (∀ v,(v,v)∉F) →
        ∀ dec : FixedMenu F reg P d i q→ZMod 2,
        ∃ σ,dec (actualFixedMenu F reg P d i q cap hf σ)≠(nativeCount F reg σ:ZMod 2) := by
  obtain ⟨n₀,hs⟩ := source_cutoff_exists γ hγ
  refine ⟨n₀,?_⟩
  intro W _ _ F reg f hN P d i q cap hf hd variance hE hloop dec
  by_contra! hgood
  have hcap := cap.trans (le_of_eq (congrArg (fun a : ℕ => a+1-i.val.val)
    (actual_printed_a (f:=f) F reg)))
  have hb := hs (Fintype.card W) i.val.val q hN hcap
  rw [← exact_printed_tape F reg i q] at hb
  exact not_le_of_gt hb (original_N8_physical_cut F reg P d i q cap hf hd variance γ hγ.le hE hloop dec hgood)

#print axioms original_N8_printed_failure

end
end V8NativeMessage.N8Literal
