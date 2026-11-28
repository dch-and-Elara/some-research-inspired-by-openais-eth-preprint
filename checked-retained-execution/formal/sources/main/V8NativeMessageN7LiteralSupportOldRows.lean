import V8NativeMessageN7LiteralSupportGenericRows
import V8NativeMessageN7LiteralSupportOrientation

/-! Specialize the exact two-cube row-fibre algebra to the original
old-row orientation of the genuine four-clone root. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical Polynomial BigOperators
open Polynomial P11FullPacking J6R10Repack J6R9PacketTiles
open Paper5.HybridClosure Paper5.D1Literal
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 10000000
set_option maxRecDepth 2300
noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {a : ℕ} {R : Type} [CommRing R]
local notation "E" => (DWire F)
local notation "D" => (MainClonedCNF.Port F)
local notation "N" => (dNetwork F reg)


def literalRowFactor (σ : W→Bool) (b : E→R) (u : DOld F) : R :=
  genericRowFactor N (oldRowTruth F reg σ) b u

def keepsSubdivision (y : E→Bool) : Bool :=
  decide (∀ p : D,y (p,false)=y (p,true))

omit [DecidableEq W] in
theorem all_one_subdivision_columns : keepsSubdivision F (fun _=>true) = true :=
  decide_eq_true (fun _=>rfl)

private theorem column_indicator_is_exact (σ : W→Bool) (y : E→Bool) :
    colKeep N (oldRowTruth F reg σ) y = keepsSubdivision F y := by
  unfold colKeep keepsSubdivision
  have h (p : D) : oldRowTruth F reg σ (.inr p) (fun w=>y (edge w.val))=true ↔
      y (p,false)=y (p,true) := by
    change decide (y (p,false)=y (p,true))=true ↔ _
    exact decide_eq_true_iff
  exact decide_eq_decide.mpr (forall_congr' h)

theorem actual_old_rows_summed
    (P : PhysicalPacking (dNetwork F reg) a (Fin 64)) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val) (κ : R) (σ : W→Bool) :
    signedRoot P i t κ (oldRowTruth F reg σ)=
      ∑ y : E→Bool, if keepsSubdivision F y then
        ∏ u : DOld F,literalRowFactor F reg σ (fun r : DWire F => coefficientAt («E»:=DWire F) (A:=DOld F)
          (B:=MainClonedCNF.Port F) (G:=Fin 64) (R:=R) («N»:=dNetwork F reg) P t κ y r) u else 0 := by
  rw [full_root_at_zero_has_literal_two_cubes P i ht hv κ (oldRowTruth F reg σ),
    flat_row_fibres_integrate P t κ (oldRowTruth F reg σ)]
  refine Finset.sum_congr rfl fun y _=>?_
  rw [column_indicator_is_exact F reg σ y]
  rfl

end
end V8NativeMessage.N7LiteralSupport
#check @V8NativeMessage.N7LiteralSupport.coefficientAt
#check @V8NativeMessage.N7LiteralSupport.literalRowFactor
#print axioms V8NativeMessage.N7LiteralSupport.all_one_subdivision_columns
#print axioms V8NativeMessage.N7LiteralSupport.actual_old_rows_summed
