import J6R34ChildPathOrdinal
import J6R34ChildPathWires

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 7800000

/-! Assemble the ordinal writer with the genuine R26 child edge book.
A complete serialized lineage-headers receipt remains necessary;
neither type-level identity nor a slot key implies its body. -/
namespace J6R34ChildPath
open scoped Polynomial Classical
open AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R25PreparedSupply J6R10Repack J6R11Blueprint J6R12Blueprint J6ActiveRun
open J1PPrinted J6R24MeteredRecursion J6R26DescriptorTree

def writeActualChild {w : ℕ} (group : Word 6) (header : List (PortRow w))
    (requests : List (WireRequest w)) : Meter (Option (List WireRead)) :=
  let was := selectedEdgeBook group header
  let out := emitWires was.result requests
  ⟨out.result,was.steps+out.steps+4⟩

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf) (v : Ticket sel r)

theorem real_child_wire_tape {port edgeW depth prec tc tz tm : ℕ}
    (J : NativeJob T v port edgeW depth prec tc tz tm)
    (tgt : v.child.host.Row⊕v.child.host.Col)
    (ports : List (PortAt (point v.child.host tgt)))
    (headAt : PortAt (point v.child.host tgt)→List Bool)
    (incoming : List (WireRequest port))
    (content : incoming=ports.map (fun p=>⟨childKey T v J.physical (edge p.val),headAt p⟩)) :
    let order := actualEdgeOrder T v J.physical
    let slot := fun p : PortAt (point v.child.host tgt)=>order.symm (edge p.val)
    let op := writeActualChild J.gWord J.physical.raw incoming
    op.result=some (ports.map (fun p=>⟨headAt p,List.replicate (slot p).val true⟩)) ∧
      op.steps≤15+(J.physical.raw.map rowScanFee).sum+v.child.edges*(4*port+5)+
        (ports.map (fun p=>sourceWireFee port (slot p).val (headAt p).length)).sum := by
  let order := actualEdgeOrder T v J.physical
  let pointer := childKey T v J.physical ∘ order
  let slot (p : PortAt (point v.child.host tgt)) := order.symm (edge p.val)
  let B := selectedEdgeBook J.gWord J.physical.raw
  obtain ⟨value,_,cost⟩ := exact_child_edge_book T v J
  have key_inj : Function.Injective pointer :=
    (child_key_injective T v J.physical).comp order.injective
  have eq : incoming=ports.map (fun p=>⟨pointer (slot p),headAt p⟩) := by
    refine content.trans (List.map_congr_left (fun x _=>?_))
    simp only [pointer,slot,Function.comp_apply,Equiv.apply_symm_apply]
  obtain ⟨rVal,rFee⟩ := source_wire_tape B.result pointer key_inj value ports headAt slot incoming eq
  refine ⟨rVal,?_⟩
  let total := (ports.map (fun u=>sourceWireFee port (slot u).val (headAt u).length)).sum
  change B.steps+(emitWires B.result incoming).steps+4≤
    15+(J.physical.raw.map rowScanFee).sum+v.child.edges*(4*port+5)+total
  change B.steps≤_ at cost
  change (emitWires B.result incoming).steps=4+total at rFee
  rw [rFee]
  omega

#print axioms real_child_wire_tape
end J6R34ChildPath
