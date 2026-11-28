import V8NativeMessageN7HighBoundFullCube
import V8NativeMessageN7HighBoundPublic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 17500000
set_option maxRecDepth 2300

/-! Close the high-precision bound at the original certified unit
slot, in both literal orientations, without assuming a height or a
row-elimination receipt for the given graph. -/
namespace V8NativeMessage.N7HighBound
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P11FullPacking J6R10Repack J6R9Recursive
  J6ActiveRun J6R12Blueprint J6R11Blueprint J1PPrinted
  Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N6D V8NativeMessage.N7
  V8NativeMessage.N7LiteralSupport

noncomputable section

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}

theorem printed_unit_public_height_and_support
    (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f))
    (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool) (x : PublicSlot F reg f P d)
    (center : x.1.val=(-1)) (isZero : siteProbe F reg d x.1 x.2.1=0)
    (mode : x.2.2.val=0) :
    let i := PublicIndex F reg f d x.1
    let Z := unitInteger P i (oldRowTruth F reg σ)
    let p := sitePrecision F reg x.1
    let v := wholePublic F reg P d hf σ x
    |Z|≤(2:ℤ)^Fintype.card (DWire F)*7^Fintype.card (DWire F) ∧
    centeredBox p f hf v=Z ∧ (v=0 ↔ exactZero P i (-1) (oldRowTruth F reg σ)=0) := by
  have addr := original_public_unit_slot_value F reg P d hf hd σ x center isZero
  rw [mode,if_pos rfl] at addr
  have hM : 0<Fintype.card (DWire F) := (Nat.zero_le _).trans_lt d.active
  have hv : padicValInt 2 (-1)=(PublicIndex F reg f d x.1).val :=
    (congrArg (padicValInt 2) center.symm).trans rfl
  dsimp only
  rw [addr]
  exact true_unit_intcast_window P (oldRowTruth F reg σ) (PublicIndex F reg f d x.1) hv hM
    (sitePrecision F reg x.1) (original_high_precision_exceeds_four_edges F reg x.1) hf hd

local notation "SP" => printedParams (f:=f) (ell:=1) (oldRowSize F)
local notation "colroot" => oldColumnRoot F reg f (fun _=>false)

theorem printed_unit_opposite_height_and_support
    (Q : ColumnPacking F reg (f:=f)) (q : ColumnReady F reg (f:=f))
    (t : ColumnCenter F reg (f:=f)) (i : Fin ((SP).levelBits 0))
    (hv : padicValInt 2 t.val=i.val) (center : t.val=(-1))
    (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool) :
    let Z := unitInteger Q i (oldColumnTruth F reg σ)
    let v := originalOppositeSlot F reg Q q t i hv 0 0 hf σ
    let p := registerPrecision SP colroot t
    |Z|≤(2:ℤ)^Fintype.card (DWire F)*7^Fintype.card (DWire F) ∧
    centeredBox p f hf v=Z ∧ (v=0 ↔ exactZero Q i (-1) (oldColumnTruth F reg σ)=0) := by
  let p := registerPrecision SP colroot t
  have hu : padicValInt 2 (-1)=i.val := by simpa only [center] using hv
  have hM : 0<Fintype.card (DWire F) := (Nat.zero_le _).trans_lt q.active
  have hp : 4*Fintype.card (DWire F)<p :=
    original_high_precision_exceeds_four_edges F reg (show PublicCenter F reg f from t)
  have hSlot : originalOppositeSlot F reg Q q t i hv 0 0 hf σ=
      nativeUnitZeroSlot Q i (oldColumnTruth F reg σ) hu (4*Fintype.card W+1) p hf := by
    rcases t with ⟨s,hs⟩
    change s=(-1) at center
    subst s
    rfl
  dsimp only
  rw [hSlot]
  exact true_unit_native_slot_window Q (oldColumnTruth F reg σ) i hu hM
    (4*Fintype.card W+1) p (by omega) hp hf hd

#print axioms printed_unit_public_height_and_support
#print axioms printed_unit_opposite_height_and_support
end
end V8NativeMessage.N7HighBound
