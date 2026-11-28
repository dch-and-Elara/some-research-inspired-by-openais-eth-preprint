import J6R36ChildFramedRouteBatch

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10500000

/-! A sidecar is issued beside the very same existing native child
creation, not synthesized from an unrelated register or from an old
variable-length log. The original header projection is bit-for-bit
untouched. The structured selection/copy charges are additional. -/
namespace J6R36ChildFramedRoute
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R34ChildPath
open J6ActiveRun J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {port eW dW prec tW zW mW key ownerW page : ℕ}

structure FramedIssue (key w owner prec page : ℕ) where
  header : DirRow key
  selected : List (PortRow w)
  framed : Option (List (FramedEdge w owner key prec page))

def emitAlongsideNative
    (J : NativeJob T v port eW dW prec tW zW mW) (issued : Meter (Word key))
    (extra : List (RefRow port (Addon ownerW (dim v) key prec page))) :
    Meter (FramedIssue key port ownerW prec page) :=
  let graph := childPortsWithCount (b:=eW) J.gWord J.physical.raw
  let depth := increment J.oldDepth
  let bytes := serializeRows graph.result.1
  let receipt := writeChildHeader issued.result J.receiving depth.result graph.result.2 bytes.result
  let out := copyBytes (J.coordinates++receipt.result.bytes)
  let bill := (issued.steps+graph.steps+depth.steps+bytes.steps+receipt.steps+6)+
    out.steps+3*J.coordinates.length+5
  let framed := frameBatch extra issued.result J.receiving graph.result.1
  ⟨⟨⟨receipt.result.id,out.result⟩,graph.result.1,framed.result⟩,bill+framed.steps+7⟩

theorem issued_frame_is_same_native_occurrence
    (J : NativeJob T v port eW dW prec tW zW mW) (issued : Meter (Word key))
    (metadata : Port v.parent.host.Edge→Addon ownerW (dim v) key prec page)
    (bank : List (RefRow port (Addon ownerW (dim v) key prec page)))
    (valid : bank=J.physical.order.map (fun h=>⟨(J.physical.record h).address,metadata h⟩)) :
    let core := J.job.make issued
    let made := emitAlongsideNative J issued bank
    let rows := halfOrder T v J.physical
    made.result.header=core.result ∧ made.result.header.id=issued.result ∧
      made.result.selected=(selectPorts J.gWord J.physical.raw).result ∧
      made.result.framed=some (rows.map (fun h=>
        frameView issued.result J.receiving (J.physical.record h.val) (metadata h.val))) ∧
      made.steps=core.steps+(frameBatch bank issued.result J.receiving made.result.selected).steps+7 :=
  ⟨rfl,J.job.make_id issued,rfl,(native_frames_from_actual_selection T v J issued metadata bank valid).1,rfl⟩

#print axioms issued_frame_is_same_native_occurrence
end J6R36ChildFramedRoute
