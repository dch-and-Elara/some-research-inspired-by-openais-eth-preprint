import J6R36ChildFramedRouteRetained

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 2400
set_option maxHeartbeats 16000000

/-! One paid native retention directly prepares the exact WireRead
list required by the existing live-ancestor reader. All its lineage
bits come from the selected structured rows and a measured prefix
copy, not from a freshly asserted child incoming-list equality. -/
namespace J6R36ChildFramedRoute
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R34ChildPath
open J6ActiveRun J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion

def retainedWireRun {w owner a key prec page : ℕ}
    (group : Word 6) (raw : List (PortRow w)) (bank : List (RefRow w (Addon owner a key prec page)))
    (id : Word key) (recv : Word prec) (target : Word owner) : Meter (Option (List WireRead)) :=
  let incoming := retainedInput group raw bank id recv target
  match incoming.result with
  | none=>⟨none,incoming.steps+3⟩
  | some lines=>
    let out := writeActualChild group raw lines
    ⟨out.result,incoming.steps+out.steps+4⟩

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf) (v : Ticket sel r)
variable {w ownerW key prec page : ℕ}

noncomputable def retainedEdgeOrder
    (D : PhysicalPorts sel (ticketReady T v) v.centerAt w) (u : OldAt T v) :
    Fin v.child.edges≃(retainedMove T v u).next.host.Edge :=
  (actualEdgeOrder T v D).trans (childHalves T v)

theorem retained_framed_wire_read
    {port edgeW dW tW zW mW : ℕ}
    (J : NativeJob T v port edgeW dW prec tW zW mW) (issued : Meter (Word key))
    (oldKey : v.parent.host.Row⊕v.parent.host.Col→Word ownerW) (inj : Function.Injective oldKey)
    (prior : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page)
    (pageKey : PageAt T v→Word page)
    (bank : List (RefRow port (Addon ownerW (dim v) key prec page)))
    (represent : bank=J.physical.order.map (fun h=>⟨(J.physical.record h).address,
      addonAt T v oldKey prior pageKey h⟩))
    (u : OldAt T v) {root : Point f ell}
    (tr : Trace root (point v.parent.host u.val))
    (seed : PortAt root→List Bool)
    (body : ∀ p : PortAt (point v.parent.host u.val), (J.physical.record p.val).body=tr.literal seed p) :
    let op := retainedWireRun J.gWord J.physical.raw bank issued.result J.receiving (oldKey u.val)
    let ports := keptPorts T v J.physical u
    let extend := tr.keep (retainedMove T v u)
    let order := retainedEdgeOrder T v J.physical u
    let phase := retainedInput J.gWord J.physical.raw bank issued.result J.receiving (oldKey u.val)
    let ordinal := fun p : PortAt (retainedMove T v u).next=>order.symm (edge p.val)
    op.result=some (ports.map (fun p=>⟨extend.literal seed p,
        List.replicate (ordinal p).val true⟩)) ∧
      op.steps≤phase.steps+19+(J.physical.raw.map rowScanFee).sum+v.child.edges*(4*port+5)+
        (ports.map (fun p=>sourceWireFee port (ordinal p).val (extend.literal seed p).length)).sum := by
  let phase := retainedInput J.gWord J.physical.raw bank issued.result J.receiving (oldKey u.val)
  let ports := keptPorts T v J.physical u
  let tail := tr.keep (retainedMove T v u)
  let order := retainedEdgeOrder T v J.physical u
  let idx (p : PortAt (retainedMove T v u).next) := order.symm (edge p.val)
  let edgeWord (j : Fin v.child.edges) := (J.physical.record (order j).val).address
  let input : List (WireRequest port) := ports.map (fun p=>⟨(J.physical.record (edge p.val).val).address,tail.literal seed p⟩)
  let keys := selectedEdgeBook J.gWord J.physical.raw
  have hR : phase.result=some input := (actual_retained_request_file T v J issued oldKey inj
    prior pageKey bank represent u tr seed body).1
  obtain ⟨ordered,_,fee⟩ := exact_child_edge_book T v J
  have eKeys : keys.result=List.ofFn edgeWord := ordered
  have injective : Function.Injective edgeWord :=
    J.physical.distinct.comp (Subtype.val_injective.comp order.injective)
  have content : input=ports.map (fun p=>⟨edgeWord (idx p),tail.literal seed p⟩) := by
    unfold input edgeWord idx
    apply List.map_congr_left
    intro p _
    simp only [Equiv.apply_symm_apply]
  obtain ⟨done,exactFee⟩ := source_wire_tape keys.result edgeWord injective eKeys
    ports (tail.literal seed) idx input content
  unfold retainedWireRun
  dsimp only
  rw [show phase.result=_ from hR]
  refine ⟨done,?_⟩
  let tot := (ports.map (fun p=>sourceWireFee port (idx p).val (tail.literal seed p).length)).sum
  change phase.steps+(keys.steps+(emitWires keys.result input).steps+4)+4≤
    phase.steps+19+(J.physical.raw.map rowScanFee).sum+v.child.edges*(4*port+5)+tot
  change (emitWires keys.result input).steps=4+tot at exactFee
  change keys.steps≤_ at fee
  rw [exactFee]
  omega

#print axioms retained_framed_wire_read
end J6R36ChildFramedRoute
