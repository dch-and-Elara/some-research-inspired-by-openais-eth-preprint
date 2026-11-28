import J6R19RetainedBox
import J6R19RetainedFrames

/-! A real bit-stream adapter between creation-precision and current-
precision entry frames. The supplied old frame is one value already
determined by the old entry evaluator, not an implementation thereof. -/
namespace J6R19Retained
open scoped Polynomial
open A1R10 AOracleMachineTime J6R18ChildWrite J6R10Repack

def promoteFrame {p q ell oldWidth newWidth : ℕ} {old : List (Word p)} {new : List (Word q)}
    (h : old.length=new.length) (tag : J6R15ModeCost.Word newWidth)
    (bs : List Bool) : Meter (List Bool×List Bool) :=
  let x := readOldFrame old ell oldWidth bs
  let u := resizeUV h x.result.2.1
  let w := writeEntry tag u.result
  ⟨(w.result,x.result.2.2),x.steps+u.steps+w.steps+4⟩

def promoteFee (e ell p q oldWidth newWidth : ℕ) : ℕ :=
  ingressFee e ell p oldWidth+boxFee e ell p q+(4*newWidth+6*ell*(e*q+1)+16)+4

set_option maxHeartbeats 900000 in
theorem promote_frame_native {X : Type*} {q ell oldWidth newWidth : ℕ}
    {f : ℤ[X]} (hf : f.Monic) (he : 0<f.natDegree) (hq : 0<q)
    (d : CreatedEntry f ell X) (hp : 0<d.created)
    {old : List (Word d.created)} {new : List (Word q)}
    (hO : Modulus d.created hp old=NativeProbeRing.liftPoly d.created f)
    (hN : Modulus q hq new=NativeProbeRing.liftPoly q f)
    (fromTag : J6R15ModeCost.Word oldWidth) (htO : fromTag.val=d.created)
    (toTag : J6R15ModeCost.Word newWidth) (htN : toTag.val=q)
    (x : X) (v : UVBlock old ell) (hEntry : castBox hO (uvRead hp old ell v)=d.table x)
    (suffix : List Bool) :
    let hE := (size_of_monic_words hp hf hO).trans (size_of_monic_words hq hf hN).symm
    let op := promoteFrame (ell:=ell) (oldWidth:=oldWidth) hE toTag ((writeEntry fromTag v).result++suffix)
    ∃ u : UVBlock new ell,
      op.result=((writeEntry toTag u).result,suffix) ∧
      fromTag.val=d.created ∧ toTag.val=q ∧
      frameRead newWidth q new.length ell op.result.1=
        (toTag.bits,u.val.map (fun row=>row.val.map Subtype.val)) ∧
      castBox hN (uvRead hq new ell u)=d.read hf q x ∧
      op.steps≤promoteFee f.natDegree ell d.created q oldWidth newWidth := by
  let hE := (size_of_monic_words hp hf hO).trans (size_of_monic_words hq hf hN).symm
  let r := resizeUV hE v
  let op := promoteFrame (ell:=ell) (oldWidth:=oldWidth) hE toTag ((writeEntry fromTag v).result++suffix)
  obtain ⟨hV,hC⟩ := native_resize_read hf he hq d hp hO hN x v hEntry
  obtain ⟨hI,hIn⟩ := readOldFrame_exact fromTag v suffix
  obtain ⟨_,hF,hWrite⟩ := write_roundtrip toTag r.result
  have hOp : op.result=((writeEntry toTag r.result).result,suffix) := by
    simp only [op,promoteFrame,hI,r]
  refine ⟨r.result,hOp,htO,htN,?_,hV,?_⟩
  · change frameRead newWidth q new.length ell op.result.1=_
    rw [hOp]
    exact hF
  · change op.steps≤_
    change (writeEntry toTag r.result).steps=_ at hWrite
    change r.steps≤_ at hC
    change (readOldFrame old ell oldWidth ((writeEntry fromTag v).result++suffix)).steps=_ at hIn
    rw [show op.steps=ingressFee old.length ell d.created oldWidth+r.steps+
        (writeEntry toTag r.result).steps+4 by simp only [op,promoteFrame,hI,hIn,r],hWrite]
    unfold promoteFee
    rw [size_of_monic_words hp hf hO,size_of_monic_words hq hf hN]
    omega

#print axioms promote_frame_native
end J6R19Retained

