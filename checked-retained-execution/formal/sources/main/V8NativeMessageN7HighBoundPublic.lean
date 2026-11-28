import V8NativeMessageN7HighBoundSlot
import V8NativeMessageN7LiteralSupportOrientation

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 17000000
set_option maxRecDepth 2200

/-! Original public-address interfaces for the unit shift. A zero node
is either given by the actual roster or obtained by the specified extra
legal evaluation; this file does not add a node to a roster. -/
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
variable (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f))

theorem original_public_unit_slot_value
    (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool) (x : PublicSlot F reg f P d)
    (center : x.1.val=(-1)) (isZero : siteProbe F reg d x.1 x.2.1=0) :
    wholePublic F reg P d hf σ x =
      if x.2.2.val=0 then
        (unitInteger P (PublicIndex F reg f d x.1) (oldRowTruth F reg σ):
          Residue f 1 (sitePrecision F reg x.1))
      else 0 := by
  have h := original_public_full_zero_probe F reg P d hf hd σ x isZero
  have k : exactZero P (PublicIndex F reg f d x.1) x.1.val (oldRowTruth F reg σ) =
      exactZero P (PublicIndex F reg f d x.1) (-1) (oldRowTruth F reg σ) :=
    congrArg (fun t : ℤ => exactZero P (PublicIndex F reg f d x.1) t (oldRowTruth F reg σ)) center
  rw [k,exact_unit_integer,J6ZeroTransport.reduceAt_int] at h
  exact h

theorem original_public_unit_slot_centered
    (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool) (x : PublicSlot F reg f P d)
    (center : x.1.val=(-1)) (isZero : siteProbe F reg d x.1 x.2.1=0)
    (mode : x.2.2.val=0)
    {V : Type*} (rows : Finset V) (keep : (DWire F→Bool)→Bool) (r : V→(DWire F→Bool)→ℤ)
    (shape : unitInteger P (PublicIndex F reg f d x.1) (oldRowTruth F reg σ)=
      columnContraction rows keep r)
    (hRows : rows.card≤Fintype.card (DWire F)) (hRow : ∀ y v, v∈rows → |r v y|≤7) :
    let i := PublicIndex F reg f d x.1
    let Z := unitInteger P i (oldRowTruth F reg σ)
    let p := sitePrecision F reg x.1
    let v := wholePublic F reg P d hf σ x
    |Z|≤(2:ℤ)^Fintype.card (DWire F)*7^Fintype.card (DWire F) ∧
      centeredBox p f hf v=Z ∧ (v=0 ↔ exactZero P i (-1) (oldRowTruth F reg σ)=0) := by
  have addr := original_public_unit_slot_value F reg P d hf hd σ x center isZero
  rw [mode,if_pos rfl] at addr
  have hM : 0<Fintype.card (DWire F) := (Nat.zero_le _).trans_lt d.active
  dsimp only
  rw [addr]
  exact unit_received_after_eliminating_rows P (PublicIndex F reg f d x.1) (oldRowTruth F reg σ)
    rows keep r shape hRows hRow hM (sitePrecision F reg x.1)
    (original_high_precision_exceeds_four_edges F reg x.1) hf hd

local notation "SP" => printedParams (f:=f) (ell:=1) (oldRowSize F)
local notation "colroot" => oldColumnRoot F reg f (fun _=>false)

theorem opposite_unit_slot_centered
    (Q : ColumnPacking F reg (f:=f)) (q : ColumnReady F reg (f:=f))
    (t : ColumnCenter F reg (f:=f)) (i : Fin ((SP).levelBits 0))
    (hv : padicValInt 2 t.val=i.val) (center : t.val=(-1))
    (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool)
    {V : Type*} (rows : Finset V) (keep : (DWire F→Bool)→Bool) (r : V→(DWire F→Bool)→ℤ)
    (shape : unitInteger Q i (oldColumnTruth F reg σ)=columnContraction rows keep r)
    (hRows : rows.card≤Fintype.card (DWire F)) (hRow : ∀ y v, v∈rows → |r v y|≤7) :
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
  exact original_unit_zero_probe_centered Q i (oldColumnTruth F reg σ) hu
    (4*Fintype.card W+1) p (by omega) hf hd rows keep r shape hRows hRow hM hp

#print axioms original_public_unit_slot_value
#print axioms original_public_unit_slot_centered
#print axioms opposite_unit_slot_centered
end
end V8NativeMessage.N7HighBound
