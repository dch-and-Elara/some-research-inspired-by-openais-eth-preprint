import V8NativeMessageN7LiteralSupportNativeComponent
import V8NativeMessageN7LiteralSupportSourceKill

/-! A row-side pin that does not receive any real shifted wire prevents
the true any-probe zero-mode parity from realizing the exterior target. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking J6R10Repack J6R9PacketTiles J6R9Recursive DenominatorBudget
open J6ActiveRun J6R12Blueprint J6R11Blueprint
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D V8NativeMessage.N7
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7000000
set_option maxRecDepth 2600
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V×V)) (baseCubic : ∀ v,GraphCutMoments.degree E v=3)
variable (loopless : ∀ v,(v,v)∉E)
local notation "F" => replacedEdges E baseCubic
local notation "hF" => replaced_cubic E baseCubic loopless
variable {f : ℤ[X]}

theorem native_old_row_parity_requires_all_original_pins
    (P : RootPacking (replacedEdges E baseCubic)
      (replaced_cubic E baseCubic loopless) f)
    (d : N6PublicReady F hF (f:=f)) (hf : f.Monic) (hd : 0<f.natDegree)
    (x : PublicSlot F hF f P d) (zeroMode : x.2.2.val=0)
    (correct : ∀ σ,
      observe f (sitePrecision F hF x.1) 1 (register_positive d x.1)
        (wholePublic F hF P d hf σ x)=UD E baseCubic (Residue f 1 1) σ) :
    ∀ v : TriVertex V,∃ q,Matches P x.1.val (sourceUnaryWire F v) q := by
  intro v
  by_contra absent
  have nz : (1:Residue f 1 1)≠0 := by
    intro h
    have bad := (V8NativeMessage.N7HighBound.integer_box_zero_iff_of_height 1 (by decide)
      f hf hd 1 (by decide)).mp (by simpa only [Int.cast_one] using h)
    exact (by decide : (1:ℤ)≠0) bad
  have kill : exactZero P (PublicIndex F hF f d x.1) x.1.val (oldRowTruth F hF (fun _=>true))=0 := by
    rw [exactZero,full_signed_root_is_zero_polynomial,full_root_at_zero_has_literal_two_cubes P
      (PublicIndex F hF f d x.1) (centerNonzero x.1) rfl,
      actual_positive_unary_source_zero F hF P _ _ (fun _=>true) v rfl absent]
  have good := correct (fun _=>true)
  rw [original_zero_mode_is_same_physical_parity_at_any_probe F hF P d hf hd _ x zeroMode,kill,map_zero] at good
  have same : UD E baseCubic (Residue f 1 1) (fun _=>true)=1 := by
    unfold UD
    exact Finset.prod_eq_one (fun _ _=>rfl)
  rw [same] at good
  exact nz good.symm

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.native_old_row_parity_requires_all_original_pins
