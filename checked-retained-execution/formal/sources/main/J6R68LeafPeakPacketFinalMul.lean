import J6R68LeafPeakPacketEndpoint
import J6R50NonModeScratchNative

/-! The actual last creation-time multiply of the packet coefficient
and the source moments. This does not replace its local arrays by the
different outer row multiplier or run the packet twice. -/
namespace J6R68.LeafPeak.Packet
open scoped Polynomial
open AOracleMachineTime A1R10 J6R21Leaf J6R21Ancestor J6R33StatefulArithmeticPage
open J6R50NonModeScratch
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 9500000
set_option Elab.async false

namespace LivePageHit
variable {f : ℤ[X]} {ell key prec tw bw page : ℕ}
variable {B : PageBank f ell key prec tw bw page}
variable {id : J6R15ModeCost.Word key} {pg : J6R15ModeCost.Word page}
variable (Q : LivePageHit B id pg)

theorem actual_created_packet_final_multiply_arrays
    (pos : 0<ell) (d : ℕ) (wires : List WireRead) (bits : List Bool)
    (prev : List (UBlock Q.S.old)) (x : UBlock Q.S.old) (xs : List (UBlock Q.S.old))
    (cut : (Q.coefficient pos d wires bits).result.val=prev++(x::xs)) :
    let L := (Q.coefficient pos d wires bits).result
    let R := (Q.moments pos d wires bits).result
    let D := (Q.createdValue pos d wires bits).result
    let ar := (encodeArrays scalarPayload (combineArrays (uGates Q.S.pPos Q.S.old) x xs R.val)).length
    D.val=(convolve (uGates Q.S.pPos Q.S.old) L.val R.val).result.drop ell ∧
    (leafPayload L).length+(leafPayload R).length+ar+(leafPayload D).length≤13*Q.W := by
  let L := (Q.coefficient pos d wires bits).result
  let R := (Q.moments pos d wires bits).result
  let D := (Q.createdValue pos d wires bits).result
  let ar := (encodeArrays scalarPayload (combineArrays (uGates Q.S.pPos Q.S.old) x xs R.val)).length
  have computes : D=(uvMul Q.S.pPos L R).result :=
    (Q.creation_uses_exact_coefficient_and_moments pos d wires bits).1
  have a : ar≤(10*ell)*(Q.S.old.length*Q.S.p) :=
    native_v_convolution_scratch Q.S.pPos L R prev x xs cut
  refine ⟨?_,?_⟩
  · change D.val=_
    exact congrArg (fun z : UVBlock Q.S.old ell=>z.val) computes
  · change (leafPayload L).length+(leafPayload R).length+ar+(leafPayload D).length≤_
    rw [leaf_payload_width,leaf_payload_width,leaf_payload_width]
    calc
      _ ≤ ell*(Q.S.old.length*Q.S.p)+ell*(Q.S.old.length*Q.S.p)+
          (10*ell)*(Q.S.old.length*Q.S.p)+ell*(Q.S.old.length*Q.S.p) :=
        Nat.add_le_add_right (Nat.add_le_add_left a _) _
      _ = _ := by unfold W; ring

#print axioms actual_created_packet_final_multiply_arrays
end LivePageHit
end J6R68.LeafPeak.Packet
