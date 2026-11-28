import J6R50NonModeScratchDense
import J6R21LeafWidth

/-! Specializations at the three literal internal coefficient levels of
the actual U/V/jet multiplication stack. Each selected stage has one
lower-level scalar operation at a time; no total heap claim is made. -/
namespace J6R50NonModeScratch
open A1R10 AOracleMachineTime J6R22Active J6R21Leaf
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

variable {p ell k : ℕ} {fw : List (A1R10.Word p)}

theorem native_u_convolution_scratch (hp : 0<p) (left right : UBlock fw)
    (pref : List (A1R10.Word p)) (x : A1R10.Word p) (xs : List (A1R10.Word p))
    (whole : left.val=pref++(x::xs)) :
    (encodeArrays Subtype.val (combineArrays (wordOps p hp).toGates x xs right.val)).length≤
      (10*fw.length)*p := by
  have b := suffix_combine_payload_bound (wordOps p hp) Subtype.val p
    (fun z=>z.property) pref x xs right.val
  rw [←whole,left.property,right.property] at b
  exact b.trans_eq (by ring)

theorem native_v_convolution_scratch (hp : 0<p) (left right : UVBlock fw ell)
    (pref : List (UBlock fw)) (x : UBlock fw) (xs : List (UBlock fw))
    (whole : left.val=pref++(x::xs)) :
    (encodeArrays scalarPayload (combineArrays (uGates hp fw) x xs right.val)).length≤
      (10*ell)*(fw.length*p) := by
  have b := suffix_combine_payload_bound (uOps hp fw) scalarPayload (fw.length*p)
    scalar_payload_width pref x xs right.val
  rw [←whole,left.property,right.property] at b
  exact b.trans_eq (by ring)

theorem native_jet_convolution_scratch (hp : 0<p) (he : 0<fw.length)
    (left right : JetTape fw ell k) (pref : List (UVBlock fw ell))
    (x : UVBlock fw ell) (xs : List (UVBlock fw ell))
    (whole : left.val=pref++(x::xs)) :
    (encodeArrays leafPayload (combineArrays (jetGates hp he ell) x xs right.val)).length≤
      (10*k)*(ell*(fw.length*p)) := by
  have b := suffix_combine_payload_bound (jetOps hp he ell) leafPayload (ell*(fw.length*p))
    leaf_payload_width pref x xs right.val
  rw [←whole,left.property,right.property] at b
  exact b.trans_eq (by ring)

#print axioms native_u_convolution_scratch
#print axioms native_v_convolution_scratch
#print axioms native_jet_convolution_scratch
end J6R50NonModeScratch
