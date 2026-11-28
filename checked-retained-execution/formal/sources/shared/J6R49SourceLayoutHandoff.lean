import J6R49SourceLayoutInstall

/-! A single optional byte handoff returns both genuine resident
layout and genuine new port bytes. The greedy setup is charged once,
not once for each projection of the resident result. -/
namespace J6R49SourceLayout
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R27OriginalGate
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun P11FullPacking J6R9PacketScopes
open J6R32ChildResidentTransfer J6R48RawRoute J6R34RootAtlas
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7200000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

def handoffWithOneLayout {a q w owner key prec page : ℕ}
    (out : Meter (Option (PreparedSeats a q)))
    (frames : Option (List (FramedEdge w owner key prec page))) :
    Meter (Option (ChildResidents a q×List (PortRow (w+1)))) :=
  match out.result,frames with
  | some field,some prior =>
    let wire := writeNextRows prior field.ordered
    ⟨wire.result.map (fun xs=>(field.native,xs)),out.steps+wire.steps+8⟩
  | _,_ => ⟨none,out.steps+3⟩

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {Q : Birth T v key prec tw bw page}
variable {previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
variable {S : SiteInputs Q previous}
variable {q : ℕ} {u : (Plan sel).Slot v.child}
local notation "d" => (ticketReady T (successorTicket v u))
local notation "t" => (Ticket.centerAt (successorTicket v u))

theorem actual_handoff_is_single_layout_operation
    {out : Meter (Option (PreparedSeats ((printedParams (f:=f) (ell:=ell) s).levelBits v.child.depth) q))}
    (X : GeneratedChild (q:=q) S d t out) (chosen : X.chart=packing sel d) :
    let D := adjacentOfGenerated (q:=q) (u:=u) X chosen
    let W := handoffWithOneLayout out S.write.result.framed
    W.result=some (X.data.native,D.generated.result.raw) ∧
      W.steps=out.steps+D.generated.steps+6 := by
  let D := adjacentOfGenerated (q:=q) (u:=u) X chosen
  let J := emitFromPrepared out S.write.result.framed
  have H := emitted_from_the_actual_prepared_port_tape (u:=u) X chosen
  have same : handoffWithOneLayout out S.write.result.framed =
      ⟨J.result.map (fun xs=>(X.data.native,xs)),J.steps+3⟩ := by
    unfold J handoffWithOneLayout emitFromPrepared
    rw [X.success,source_framed_in_child_order S]
  rw [same]
  constructor
  · change J.result.map _=_
    rw [show J.result=some D.generated.result.raw from H.1]
    rfl
  · change J.steps+3=_
    rw [show J.steps=out.steps+D.generated.steps+3 from H.2]

#print axioms actual_handoff_is_single_layout_operation
end
end J6R49SourceLayout