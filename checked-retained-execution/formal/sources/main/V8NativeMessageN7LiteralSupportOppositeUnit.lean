import V8NativeMessageN7LiteralSupportColumnPositive
import V8NativeMessageN7HighBoundPrinted
import V8NativeMessageN6DTarget

/-! The same opposite native zero mode is nonzero for every sign word
at the real unit shift, not merely an equivalent rational count. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial DenominatorBudget P11FullPacking J6R10Repack J6R9Recursive
open J6ActiveRun J6R12Blueprint J6R11Blueprint J1PPrinted
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D V8NativeMessage.N7
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 15000000
set_option maxRecDepth 2300
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "SP" => printedParams (f:=f) (ell:=1) (oldRowSize F)
local notation "root" => oldColumnRoot F reg f (fun _=>false)

theorem literal_opposite_unit_has_full_support
    (P : ColumnPacking F reg (f:=f)) (d : ColumnReady F reg (f:=f))
    (t : ColumnCenter F reg (f:=f)) (i : Fin ((SP).levelBits 0))
    (hv : padicValInt 2 t.val=i.val) (unit : t.val=(-1))
    (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool) :
    originalOppositeSlot F reg P d t i hv 0 0 hf σ≠0 := by
  have hParity : padicValInt 2 (-1)=i.val := by
    rw [←unit]
    exact hv

  have pos := true_old_columns_strictly_positive F reg P (by decide : (-1:ℤ)≠0)
    i hParity (by norm_num : (-1:ℚ)<0) σ
  have hReal : 0<twoLocalRat (exactZero P i (-1) (oldColumnTruth F reg σ)) := by
    rw [exactZero,full_signed_root_is_zero_polynomial,map_signed_root,rho_at_actual_unit_shift,map_neg,map_one]
    exact pos
  have witness := V8NativeMessage.N7HighBound.printed_unit_opposite_height_and_support
    F reg P d t i hv unit hf hd σ
  intro z
  have h := witness.2.2.mp z
  rw [h,map_zero] at hReal
  exact (lt_irrefl _ hReal)

theorem literal_opposite_nonzero_mode_vanishes
    (P : ColumnPacking F reg (f:=f)) (d : ColumnReady F reg (f:=f))
    (t : ColumnCenter F reg (f:=f)) (i : Fin ((SP).levelBits 0))
    (hv : padicValInt 2 t.val=i.val)
    (β : J6R9PacketScopes.Mode i (registerPrecision SP root t) P.mask →₀ ℕ) (nz : β≠0)
    (hf : f.Monic) (σ : W→Bool) :
    originalOppositeSlot F reg P d t i hv 0 β hf σ=0 :=
  native_zero_probe_nonzero_mode P i (centerNonzero t) hv _ _
    (oldColumnFile F reg f σ) hf β nz

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.literal_opposite_unit_has_full_support
#print axioms V8NativeMessage.N7LiteralSupport.literal_opposite_nonzero_mode_vanishes
