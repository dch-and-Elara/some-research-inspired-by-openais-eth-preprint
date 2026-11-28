import V8NativeMessageN7LiteralSupportOldRowSupport
import V8NativeMessageN7LiteralSupportOddRead
import V8NativeMessageN7HighBoundPrinted

/-! Unit shift and small odd displacement support at the same literal
old-row public address. This does not assert that any roster has a zero
probe; it starts with exactly that legal address. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial DenominatorBudget P1DyadicGrid P11FullPacking J6R10Repack J6R9Recursive
open J6R9PacketCoeff J6ActiveRun J6R12Blueprint J6R11Blueprint J1PPrinted
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D V8NativeMessage.N7
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 13000000
set_option maxRecDepth 2500
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "SP" => printedParams (f:=f) (ell:=1) (oldRowSize F)
local notation "a" => (J6ActiveRun.Shape.levelBits (SP) 0)
local notation "u" => (J6ActiveRun.Shape.levelWidth (SP) 0)
variable (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f))

theorem original_old_row_unit_exact_support
    (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool)
    (x : PublicSlot F reg f P d) (ct : x.1.val=(-1))
    (z : siteProbe F reg d x.1 x.2.1=0) (mode : x.2.2.val=0) :
    wholePublic F reg P d hf σ x≠0 ↔ oldRowSupported F reg P (-1) σ := by
  have slot := (V8NativeMessage.N7HighBound.printed_unit_public_height_and_support
    F reg P d hf hd σ x ct z mode).2.2
  let i := PublicIndex F reg f d x.1
  have hv : padicValInt 2 (-1)=i.val :=
    (congrArg (padicValInt 2) ct.symm).trans rfl
  have odd : Odd (-1:ℤ) := ⟨-1,by decide⟩
  exact (not_congr slot).trans (actual_old_row_odd_exact_support F reg P i
    (by decide) hv (neg_one_in_signed_grid a) odd σ)

theorem original_old_row_small_odd_exact_support
    (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool)
    (x : PublicSlot F reg f P d) (odd : Odd x.1.val)
    (z : siteProbe F reg d x.1 x.2.1=0) (mode : x.2.2.val=0)
    (small : clearedExponent a x.1.val*u<24*2^a) :
    wholePublic F reg P d hf σ x≠0 ↔ oldRowSupported F reg P x.1.val σ := by
  have slot := original_small_odd_zero_mode_preserves_exact_support F reg P d hf hd σ x odd z mode small
  exact (not_congr slot).trans
    (actual_old_row_odd_exact_support F reg P (PublicIndex F reg f d x.1)
      (centerNonzero x.1) rfl (public_center_in_grid F reg x.1) odd σ)

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.original_old_row_unit_exact_support
#print axioms V8NativeMessage.N7LiteralSupport.original_old_row_small_odd_exact_support
