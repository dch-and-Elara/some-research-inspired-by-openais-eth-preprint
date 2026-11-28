import V8NativeMessageN7LiteralSupportPublicParity
import V8NativeMessageN7LiteralSupportOrientation

/-! Observation of the original oppositely oriented completed zero
mode at its actual printed precision, with the same source root file. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial DenominatorBudget P11FullPacking J6R10Repack J6R9Recursive
open J6ActiveRun J6R12Blueprint J6R11Blueprint J1PPrinted
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D V8NativeMessage.N7
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 11000000
set_option maxRecDepth 2500
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "SP" => printedParams (f:=f) (ell:=1) (oldRowSize F)
local notation "croot" => oldColumnRoot F reg f (fun _=>false)

def oppositePrintedPrec (t : ColumnCenter F reg (f:=f)) : ℕ := registerPrecision SP croot t

theorem opposite_printed_precision_positive (t : ColumnCenter F reg (f:=f)) :
    1≤oppositePrintedPrec F reg t :=
  Nat.succ_le_of_lt ((Nat.zero_le _).trans_lt
    (original_high_precision_exceeds_four_edges F reg (show PublicCenter F reg f from t)))

def oppositePrintedParityMap (t : ColumnCenter F reg (f:=f)) : TwoLocal→+*Residue f 1 1 :=
  let p := oppositePrintedPrec F reg t
  (observe f p 1 (opposite_printed_precision_positive F reg t)).comp
    (J6ZeroTransport.reduceAt p (J6R10Integral.box_two_nil p f 1))

theorem literal_opposite_zero_mode_same_parity_at_any_probe
    (P : ColumnPacking F reg (f:=f)) (d : ColumnReady F reg (f:=f))
    (t : ColumnCenter F reg (f:=f)) (i : Fin ((SP).levelBits 0))
    (hv : padicValInt 2 t.val=i.val) (z : Residue f 1 (oppositePrintedPrec F reg t))
    (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool) :
    observe f (oppositePrintedPrec F reg t) 1 (opposite_printed_precision_positive F reg t)
       (originalOppositeSlot F reg P d t i hv z 0 hf σ) =
    oppositePrintedParityMap F reg t (exactZero P i t.val (oldColumnTruth F reg σ)) := by
  let p := oppositePrintedPrec F reg t
  let n := J6R10Integral.box_two_nil p f 1
  let ψ := observe f p 1 (opposite_printed_precision_positive F reg t)
  let file := V8PooledMenu.binaryFile f (4*Fintype.card W+1) (oldColumnTruth F reg σ)
  change ψ (V8PooledMenu.slot P i (centerNonzero t) hv p n z file hf 0)=_
  calc
    _ = ψ (V8PooledMenu.slot P i (centerNonzero t) hv p n 0 file hf 0) :=
      zero_mode_same_probe_mod_two P i (centerNonzero t) hv p n file hf z 0 ψ
        (by simpa only [pow_one] using J6R10Integral.box_two_nil 1 f 1)
    _ = _ := congrArg ψ (actual_zero_slot_is_reduction P i (centerNonzero t) hv _
      (4*Fintype.card W+1) p (by omega) hf hd)

end
end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.opposite_printed_precision_positive
#print axioms V8NativeMessage.N7LiteralSupport.literal_opposite_zero_mode_same_parity_at_any_probe
