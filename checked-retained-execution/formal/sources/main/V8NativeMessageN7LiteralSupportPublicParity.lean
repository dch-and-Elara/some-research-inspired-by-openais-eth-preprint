import V8NativeMessageN7LiteralSupportZero
import V8NativeMessageN7LiteralSupportComponentFactor

/-! The true public zero-mode reply at any legal probe uses exactly
the same partial-wiring parity. No new sampled roster point is assumed. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial DenominatorBudget P11FullPacking J6R10Repack J6R9Recursive
open J6ActiveRun J6R12Blueprint J6R11Blueprint J1PPrinted
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D V8NativeMessage.N7
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 12500000
set_option maxRecDepth 2500
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]} (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f))

def printedZeroParityMap (t : PublicCenter F reg f) : TwoLocal→+*Residue f 1 1 :=
  let p := sitePrecision F reg t
  (observe f p 1 (register_positive d t)).comp
    (J6ZeroTransport.reduceAt p (J6R10Integral.box_two_nil p f 1))

theorem original_zero_mode_is_same_physical_parity_at_any_probe
    (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool)
    (x : PublicSlot F reg f P d) (zeroMode : x.2.2.val=0) :
    observe f (sitePrecision F reg x.1) 1 (register_positive d x.1)
      (wholePublic F reg P d hf σ x) =
    printedZeroParityMap F reg d x.1
      (exactZero P (PublicIndex F reg f d x.1) x.1.val (oldRowTruth F reg σ)) := by
  let p := sitePrecision F reg x.1
  let i := PublicIndex F reg f d x.1
  let hnil := J6R10Integral.box_two_nil p f 1
  let ψ := observe f p 1 (register_positive d x.1)
  let literalFile := V8PooledMenu.binaryFile f (4*Fintype.card W+1) (oldRowTruth F reg σ)
  have h₂ : (2:Residue f 1 1)=0 := by
    simpa only [pow_one] using J6R10Integral.box_two_nil 1 f 1
  rw [publicSlot_is_literal,zeroMode]
  change ψ (V8PooledMenu.slot P i (centerNonzero x.1) rfl p hnil
    (siteProbe F reg d x.1 x.2.1) literalFile hf 0)=_
  calc
    _ = ψ (V8PooledMenu.slot P i (centerNonzero x.1) rfl p hnil 0 literalFile hf 0) :=
      zero_mode_same_probe_mod_two P i (centerNonzero x.1) rfl p hnil literalFile hf _ 0 ψ h₂
    _ = _ := congrArg ψ (actual_zero_slot_is_reduction P i (centerNonzero x.1) rfl _
      (4*Fintype.card W+1) p (by omega) hf hd)

theorem original_public_parity_factors_by_true_component_partition {K : Type} [Fintype K]
    (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool)
    (x : PublicSlot F reg f P d) (zeroMode : x.2.2.val=0)
    (color : DOld F⊕MainClonedCNF.Port F→K)
    (uncut : ∀ {r q},Matches P x.1.val r q→color (.inl ((dNetwork F reg).row r))=
      color (.inr ((dNetwork F reg).col q))) :
    observe f (sitePrecision F reg x.1) 1 (register_positive d x.1)
      (wholePublic F reg P d hf σ x)=
      ∏ k,literalComponentFactors P x.1.val color (oldRowTruth F reg σ) k := by
  rw [original_zero_mode_is_same_physical_parity_at_any_probe F reg P d hf hd σ x zeroMode]
  exact factor_actual_parity_wiring P (PublicIndex F reg f d x.1) (centerNonzero x.1) rfl
    (public_center_in_grid F reg x.1) (printedZeroParityMap F reg d x.1)
    (by simpa only [pow_one] using J6R10Integral.box_two_nil 1 f 1)
    color uncut (oldRowTruth F reg σ)

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.original_zero_mode_is_same_physical_parity_at_any_probe
#print axioms V8NativeMessage.N7LiteralSupport.original_public_parity_factors_by_true_component_partition
