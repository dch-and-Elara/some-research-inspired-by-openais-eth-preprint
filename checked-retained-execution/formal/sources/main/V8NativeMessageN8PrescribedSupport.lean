import V8NativeMessageN8PrescribedChart
import V8NativeMessageN8LiteralPrinted

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1450000
set_option maxRecDepth 2450

/-! Pointwise v8 N8 transfer to the prescribed legal binary lifts.
The completed slot still uses its original high precision and every
weighted mode. Projection is into the same N8 receiver as before. -/
namespace V8NativeMessage.N8Prescribed
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P11FullPacking J6R10Repack J6R9Recursive
open J6ActiveRun J6R12Blueprint J6R11Blueprint
open Paper5.D1Literal Paper5.HybridClosure V8NativeMessage.N6D V8NativeMessage.N7
open V8NativeMessage.N8Literal

noncomputable section
variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
variable (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f)) (i : rootKept F f)
variable (B : Chart (f:=f) F reg i)
variable (q : ℕ) (cap : q≤(printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0+1-i.val.val)

def prescribedLowProbe (t : Centers (f:=f) F reg i) (z : PublicProbe F reg f) : Residue f 1 q :=
  receiveAt (f:=f) F reg d i q cap t (prescribedNode (f:=f) F reg i B t z)

def actualPrescribedMenu (hf : f.Monic) (σ : W→Bool) : FixedMenu (f:=f) F reg P d i q :=
  fun t z β=>receiveAt (f:=f) F reg d i q cap t (prescribedWhole (f:=f) F reg d i B P hf σ t z β)

theorem frozen_projected_menu_is_original (hf : f.Monic) (σ : W→Bool) :
    actualPrescribedMenu (f:=f) F reg P d i (frozenChart (f:=f) F reg d i) q cap hf σ =
      actualFixedMenu (f:=f) F reg P d i q cap hf σ := by
  funext t z β
  exact congrArg (receiveAt (f:=f) F reg d i q cap t)
    (frozen_product_is_original (f:=f) F reg d i P hf σ t z β)

/-- The same literal created child, at an explicit scalar argument.
This helper isolates the pointwise kernel from finite chart indexing. -/
def sourceSlotAt (hf : f.Monic) (σ : W→Bool)
    (t : Centers (f:=f) F reg i) (ζ : Residue f 1 (sitePrecision (f:=f) F reg t.val))
    (β : PublicMenu F reg f P d t.val) : Residue f 1 (sitePrecision (f:=f) F reg t.val) :=
  let p := sitePrecision (f:=f) F reg t.val
  V8PooledMenu.slot P (PublicIndex F reg f d t.val) (centerNonzero t.val) rfl
    p (J6R10Integral.box_two_nil p f 1) ζ (oldRowFile F reg f (4*Fintype.card W+1) σ) hf β.val

theorem pointwise_zero_eval (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool)
    (t : Centers (f:=f) F reg i) (ζ : Residue f 1 (sitePrecision (f:=f) F reg t.val))
    (β : PublicMenu F reg f P d t.val) (h0 : β.val=0) :
    let φ := receiveAt (f:=f) F reg d i q cap t
    φ (sourceSlotAt (f:=f) F reg P d i hf σ t ζ β)=
      (V8PooledMenu.wholeScaled P i.val t.val.val (oldRowTruth F reg σ)).eval₂
        (baseAt f q) (2*φ ζ) := by
  let p := sitePrecision (f:=f) F reg t.val
  let φ := receiveAt (f:=f) F reg d i q cap t
  let n := J6R10Integral.box_two_nil p f 1
  let I := PublicIndex F reg f d t.val
  have eq : φ.comp (J6ZeroTransport.reduceAt p n)=baseAt f q := J6ZeroTransport.ringHom_unique _ _
  have pos : 0<4*Fintype.card W+1 := by omega
  let T₀ := V8PooledMenu.wholeScaled P I t.val.val (oldRowTruth F reg σ)
  have z := (V8PooledMenu.wholeScaled_eval P I t.val.val (oldRowTruth F reg σ)
    (4*Fintype.card W+1) pos hf hd p n ζ φ).symm
  change φ (sourceSlotAt (f:=f) F reg P d i hf σ t ζ β)=_
  rw [sourceSlotAt,h0,V8PooledMenu.projected_zero_slot]
  exact z.trans (by
    change T₀.eval₂ (φ.comp (J6ZeroTransport.reduceAt p n)) (2*φ ζ)=_
    rw [eq,show T₀=V8PooledMenu.wholeScaled P i.val t.val.val (oldRowTruth F reg σ) from
      congrArg (fun a=>V8PooledMenu.wholeScaled P a t.val.val (oldRowTruth F reg σ))
        (index_at_coordinate (f:=f) F reg d i t)])

theorem prescribed_zero_projection (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool)
    (t : Centers (f:=f) F reg i) (z : PublicProbe F reg f) (β : PublicMenu F reg f P d t.val)
    (zero_mode : β.val=0) :
    actualPrescribedMenu (f:=f) F reg P d i B q cap hf σ t z β =
      (V8PooledMenu.wholeScaled P i.val t.val.val (oldRowTruth F reg σ)).eval₂
        (baseAt f q) (2*prescribedLowProbe (f:=f) F reg d i B q cap t z) := by
  have h := congrArg (receiveAt (f:=f) F reg d i q cap t) (prescribed_product_is_source (f:=f) F reg d i B P hf σ t z β)
  exact h.trans (pointwise_zero_eval (f:=f) F reg P d i q cap hf hd σ t (prescribedNode (f:=f) F reg i B t z) β zero_mode)

theorem pointwise_nonzero_erased (hf : f.Monic) (σ : W→Bool)
    (t : Centers (f:=f) F reg i) (ζ : Residue f 1 (sitePrecision (f:=f) F reg t.val))
    (β : PublicMenu F reg f P d t.val) (hβ : β.val≠0) :
    receiveAt (f:=f) F reg d i q cap t (sourceSlotAt (f:=f) F reg P d i hf σ t ζ β)=0 := by
  let p := sitePrecision (f:=f) F reg t.val
  have h : q≤(printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0+1-(PublicIndex F reg f d t.val).val := by
    rw [index_at_coordinate (f:=f) F reg d i t]
    exact cap
  exact V8PooledMenu.projected_nonzero_slot P (PublicIndex F reg f d t.val)
    (centerNonzero t.val) rfl p (J6R10Integral.box_two_nil p f 1) ζ _ hf β.val hβ
    (receiveAt (f:=f) F reg d i q cap t) h (J6R10Integral.box_two_nil q f 1)

theorem prescribed_nonzero_projection (hf : f.Monic) (σ : W→Bool)
    (t : Centers (f:=f) F reg i) (z : PublicProbe F reg f) (β : PublicMenu F reg f P d t.val)
    (active_mode : β.val≠0) :
    actualPrescribedMenu (f:=f) F reg P d i B q cap hf σ t z β=0 := by
  have h := congrArg (receiveAt (f:=f) F reg d i q cap t) (prescribed_product_is_source (f:=f) F reg d i B P hf σ t z β)
  exact h.trans (pointwise_nonzero_erased (f:=f) F reg P d i q cap hf σ t (prescribedNode (f:=f) F reg i B t z) β active_mode)

variable (T : Finset (Fin 64))

def decodePrescribed (msg : RowTape (f:=f) F reg i q) (y : ColWord P i T) : FixedMenu (f:=f) F reg P d i q :=
  fun t z β =>
    if β.val=0 then
      let ζ := prescribedLowProbe (f:=f) F reg d i B q cap t z
      TruncatedProbeMenu.reconstruct (msg t) ζ *
        (colPolynomial P i T t.val.val y).eval₂ (baseAt f q) (2*ζ)
    else 0

theorem same_base_scalar_tape_for_prescribed (hf : f.Monic) (hd : 0<f.natDegree)
    (x : RowWord P i T) (y : ColWord P i T) :
    actualPrescribedMenu (f:=f) F reg P d i B q cap hf (mergeSigns P i T x y)=
      decodePrescribed (f:=f) F reg P d i B q cap T (rowMessage (f:=f) F reg P i T q x) y := by
  funext t z β
  by_cases hβ : β.val=0
  · let ζ := prescribedLowProbe (f:=f) F reg d i B q cap t z
    let L := rowPolynomial P i T t.val.val x
    let R := colPolynomial P i T t.val.val y
    have e : TruncatedProbeMenu.reconstruct (V8PooledMenu.digits q L) ζ =
        L.eval₂ (baseAt f q) (2*ζ) :=
      V8PooledMenu.receive_digits (J6R10Integral.box_two_nil q f 1) (baseAt f q) L ζ
    rw [decodePrescribed,if_pos hβ]
    change _=TruncatedProbeMenu.reconstruct (V8PooledMenu.digits q L) ζ * R.eval₂ (baseAt f q) (2*ζ)
    rw [e,prescribed_zero_projection (f:=f) F reg P d i B q cap hf hd (mergeSigns P i T x y) t z β hβ,
      exact_side_split P i T t.val.val x y,Polynomial.eval₂_mul]
  · rw [prescribed_nonzero_projection (f:=f) F reg P d i B q cap hf (mergeSigns P i T x y) t z β hβ]
    simp only [decodePrescribed,if_neg hβ]

#print axioms frozen_projected_menu_is_original
#print axioms prescribed_zero_projection
#print axioms prescribed_nonzero_projection
#print axioms same_base_scalar_tape_for_prescribed
end
end V8NativeMessage.N8Prescribed