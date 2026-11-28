import V8NativeMessageN8LiteralPayload
import V8NativeMessageN8LiteralChart
import V8NativeMessageN8LiteralZero

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1250000
set_option maxRecDepth 2400

/-! Exact factorization of the original full fixed-coordinate menu:
a side tape of base scalars, the receiver's own Boolean signs, and
the unchanged original public geometry. -/
namespace V8NativeMessage.N8Literal
open scoped Classical BigOperators Polynomial
open Polynomial DenominatorBudget P11FullPacking J6R10Repack J6R9Recursive
open J6ActiveRun J6R12Blueprint
open Paper5.D1Literal Paper5.HybridClosure V8NativeMessage.N6D V8NativeMessage.N7

noncomputable section
variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀v,GraphCutMoments.degree F v=3)
variable {f : ℤ[X]}
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
variable (P : RootPacking F reg f) (d : N6PublicReady F reg (f:=f)) (i : rootKept F f)
variable (T : Finset (Fin 64)) (q : ℕ) (cap : q≤(printedParams (f:=f) (ell:=1) (oldRowSize F)).levelBits 0+1-i.val.val)

abbrev FixedMenu :=
  (t : Centers F reg i)→PublicProbe F reg f→PublicMenu F reg f P d t.val→Residue f 1 q

def receiveAt (t : Centers F reg i) : Residue f 1 (sitePrecision F reg t.val)→+*Residue f 1 q := by
  have fit : q ≤ sitePrecision (f:=f) F reg t.val :=
    coordinate_capacity_fits (f:=f) (F:=F) (reg:=reg) (d:=d) (i:=i) (t:=t) (q:=q) cap
  exact V8NativeMessage.N7.observe f (sitePrecision (f:=f) F reg t.val) q fit

def probeLow (t : Centers F reg i) (z : PublicProbe F reg f) : Residue f 1 q :=
  receiveAt F reg d i q cap t (siteProbe F reg d t.val z)

def baseAt (f : ℤ[X]) (q : ℕ) : TwoLocal→+*Residue f 1 q :=
  J6ZeroTransport.reduceAt q (J6R10Integral.box_two_nil q f 1)

def actualFixedMenu (hf : f.Monic) (σ : W→Bool) : FixedMenu F reg P d i q :=
  fun t z β => receiveAt F reg d i q cap t (wholePublic F reg P d hf σ ⟨t.val,z,β⟩)

def rowMessage (x : RowWord P i T) : RowTape F reg i q :=
  fun t => V8PooledMenu.digits q (rowPolynomial P i T t.val.val x)

def decodedMenu (msg : RowTape F reg i q) (y : ColWord P i T) : FixedMenu F reg P d i q :=
  fun t z β =>
    if β.val=0 then
      let ζ := probeLow F reg d i q cap t z
      TruncatedProbeMenu.reconstruct (msg t) ζ *
        (colPolynomial P i T t.val.val y).eval₂ (baseAt f q) (2*ζ)
    else 0

theorem literal_zero_projection (hf : f.Monic) (hd : 0<f.natDegree) (σ : W→Bool)
    (t : Centers F reg i) (z : PublicProbe F reg f) (β : PublicMenu F reg f P d t.val)
    (hzero : β.val=0) :
    actualFixedMenu F reg P d i q cap hf σ t z β =
      (V8PooledMenu.wholeScaled P i.val t.val.val (oldRowTruth F reg σ)).eval₂
        (baseAt f q) (2*probeLow F reg d i q cap t z) := by
  let ψ := receiveAt F reg d i q cap t
  let p := sitePrecision F reg t.val
  have he : ψ.comp (J6ZeroTransport.reduceAt p (J6R10Integral.box_two_nil p f 1)) =
      baseAt f q := J6ZeroTransport.ringHom_unique _ _
  let adr : PublicSlot F reg f P d := ⟨t.val,z,β⟩
  have hz : adr.2.2.val=0 := hzero
  have h := original_zero_sample_polynomial F reg P d hf hd σ adr hz ψ
  change ψ (wholePublic F reg P d hf σ adr) = _
  change ψ (wholePublic F reg P d hf σ adr) =
    (V8PooledMenu.wholeScaled P (PublicIndex F reg f d t.val) t.val.val
      (oldRowTruth F reg σ)).eval₂
        (ψ.comp (J6ZeroTransport.reduceAt p (J6R10Integral.box_two_nil p f 1)))
        (2*probeLow F reg d i q cap t z) at h
  calc
    _ = _ := h
    _ = _ := by rw [he,index_at_coordinate F reg d i t]

#print axioms literal_zero_projection

theorem literal_nonzero_projection (hf : f.Monic) (σ : W→Bool)
    (t : Centers F reg i) (z : PublicProbe F reg f) (β : PublicMenu F reg f P d t.val)
    (hβ : β.val≠0) :
    actualFixedMenu F reg P d i q cap hf σ t z β=0 := by
  have h : q≤(S).levelBits 0+1-(PublicIndex F reg f d t.val).val := by
    rw [index_at_coordinate F reg d i t]
    exact cap
  simpa only [actualFixedMenu,receiveAt] using
    original_public_nonzero_erased F reg P d hf σ ⟨t.val,z,β⟩ hβ h

#print axioms literal_nonzero_projection

theorem original_fixed_coordinate_payload (hf : f.Monic) (hd : 0<f.natDegree)
    (x : RowWord P i T) (y : ColWord P i T) :
    actualFixedMenu F reg P d i q cap hf (mergeSigns P i T x y) =
      decodedMenu F reg P d i T q cap (rowMessage F reg P i T q x) y := by
  funext t z β
  by_cases hβ : β.val=0
  · let ζ := probeLow F reg d i q cap t z
    let L := rowPolynomial P i T t.val.val x
    let R := colPolynomial P i T t.val.val y
    have e : TruncatedProbeMenu.reconstruct (V8PooledMenu.digits q L) ζ =
        L.eval₂ (baseAt f q) (2*ζ) :=
      V8PooledMenu.receive_digits (J6R10Integral.box_two_nil q f 1) (baseAt f q) L ζ
    rw [decodedMenu,if_pos hβ]
    change _=TruncatedProbeMenu.reconstruct (V8PooledMenu.digits q L) ζ *
      R.eval₂ (baseAt f q) (2*ζ)
    rw [e,literal_zero_projection F reg P d i q cap hf hd (mergeSigns P i T x y) t z β hβ,
      exact_side_split P i T t.val.val x y,Polynomial.eval₂_mul]
  · rw [literal_nonzero_projection F reg P d i q cap hf (mergeSigns P i T x y) t z β hβ]
    simp only [decodedMenu,if_neg hβ]

#print axioms original_fixed_coordinate_payload
end
end V8NativeMessage.N8Literal
