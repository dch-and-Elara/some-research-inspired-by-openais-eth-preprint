import V8NativeMessageN7LiteralSupportComponentSource
import V8NativeMessageN7LiteralSupportPublicParity
import V8NativeMessageN7HighBoundReceipt

/-! Attach the component obstruction to the same observed public native
slot, at any legal probe and without assuming a zero point in its roster. -/
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

theorem native_old_row_exterior_pair_cannot_split
    (P : RootPacking (replacedEdges E baseCubic)
      (replaced_cubic E baseCubic loopless) f)
    (d : N6PublicReady F hF (f:=f))
    (hf : f.Monic) (hd : 0<f.natDegree)
    (x : PublicSlot F hF f P d) (zeroMode : x.2.2.val=0)
    (correct : ∀ σ,
      observe f (sitePrecision F hF x.1) 1 (register_positive d x.1)
        (wholePublic F hF P d hf σ x)=UD E baseCubic (Residue f 1 1) σ)
    (e : E) :
    Connected P x.1.val (oldUnaryVertex F (seat E baseCubic e false))
      (oldUnaryVertex F (seat E baseCubic e true)) := by
  have notOne : (1:Residue f 1 1)≠0 := by
    intro h
    have bad := (V8NativeMessage.N7HighBound.integer_box_zero_iff_of_height 1 (by decide)
      f hf hd 1 (by decide)).mp (by simpa only [Int.cast_one] using h)
    exact (by decide : (1:ℤ)≠0) bad
  letI : Nontrivial (Residue f 1 1) := nontrivial_of_ne (1:Residue f 1 1) 0 notOne
  refine true_old_row_exterior_pair_in_same_wiring_component E baseCubic loopless P
    (PublicIndex F hF f d x.1) (centerNonzero x.1) rfl (public_center_in_grid F hF x.1)
    (printedZeroParityMap F hF d x.1) (by simpa only [pow_one] using J6R10Integral.box_two_nil 1 f 1)
    ?_ e
  intro σ
  exact (original_zero_mode_is_same_physical_parity_at_any_probe F hF P d hf hd σ x zeroMode).symm.trans
    (correct σ)

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.native_old_row_exterior_pair_cannot_split
