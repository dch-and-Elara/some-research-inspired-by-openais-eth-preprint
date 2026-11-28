import V8NativeMessageN7Public
import V8NativeMessageN7WeightedSlot

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

/-! Printed literal whole-slot version of the strengthened N7 gain. -/
namespace V8NativeMessage.N7
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9Recursive J6R9PacketScopes
open J6ActiveRun J6R12Blueprint Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]} (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f))

abbrev publicCost (x : PublicSlot F reg f P d) :=
  nativeModeCost P (PublicIndex F reg f d x.1) (sitePrecision F reg x.1) x.2.2.val

theorem original_public_weight (hf : f.Monic) (σ : W→Bool) (x : PublicSlot F reg f P d) :
    (2:Residue f 1 (sitePrecision F reg x.1))^publicCost F reg P d x ∣
      wholePublic F reg P d hf σ x := by
  rw [publicSlot_is_literal]
  exact actual_whole_slot_weight P (PublicIndex F reg f d x.1)
    (centerNonzero x.1) rfl (sitePrecision F reg x.1) _ _ _ hf x.2.2.val

theorem original_weight_projects_to_zero (hf : f.Monic) (σ : W→Bool) (x : PublicSlot F reg f P d)
    {q : ℕ} (hle : q≤sitePrecision F reg x.1) (budget : q≤publicCost F reg P d x) :
    observe f (sitePrecision F reg x.1) q hle (wholePublic F reg P d hf σ x)=0 := by
  rw [publicSlot_is_literal]
  exact projected_whole_slot_weight P (PublicIndex F reg f d x.1) (centerNonzero x.1)
    rfl (sitePrecision F reg x.1) _ _ _ hf x.2.2.val _ budget (J6R10Integral.box_two_nil q f 1)

#print axioms original_public_weight
#print axioms original_weight_projects_to_zero
end
end V8NativeMessage.N7
