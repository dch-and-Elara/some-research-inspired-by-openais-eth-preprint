import J6R41StructuredAllPathsInduct
import J6R53OldOwnerBorn

/-! A retained Gate opcode and its original numeric port body are not
independent certificates. The same actual parent-to-child route
transports both, including an owner with no wires. Use the very
childGate rule of the actual paid roster producer. -/
namespace J6R54TerminalBoot
open scoped Polynomial Classical
open Polynomial J6R21Ancestor J6R20Ancestor J6R34ChildPath J6R26DescriptorTree J6R15ModeCost
open J6R36ChildFramedRoute J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open J6ActiveRun J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R25PreparedSupply J6R30ProducedGateRegistry J6R41StructuredAllPaths J6R53OldOwner J6R27OriginalGate
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 34000000
set_option maxRecDepth 5100
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page wCode : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf)
variable (rootGates : r.host.Row⊕r.host.Col→Option (CodeGate (Word wCode)))

noncomputable def gateHistory :
    {c : Call (PhysicalHost f ell)} → Path sel r c →
    c.host.Row⊕c.host.Col→Option (CodeGate (Word wCode))
  | _,.root => rootGates
  | _,.step p w => childGate (T:=T) (v:=p.ticket w) (gateHistory p)

variable {T rootGates}

theorem gate_history_keeps {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c)
    (u : (p.ticket w).child.host.Row⊕(p.ticket w).child.host.Col)
    (old : OldAt T (p.ticket w)) (whereAt : childVertices T (p.ticket w) u=.inl old) :
    gateHistory T rootGates (.step p w) u=gateHistory T rootGates p old.val := by
  change childGate (T:=T) (v:=p.ticket w) (gateHistory T rootGates p) u=_
  unfold childGate
  rw [whereAt]

theorem gate_history_fresh {c : Call (PhysicalHost f ell)} (p : Path sel r c) (w : (Plan sel).Slot c)
    (u : (p.ticket w).child.host.Row⊕(p.ticket w).child.host.Col)
    (k : PageAt T (p.ticket w)) (whereAt : childVertices T (p.ticket w) u=.inr k) :
    gateHistory T rootGates (.step p w) u=none := by
  change childGate (T:=T) (v:=p.ticket w) (gateHistory T rootGates p) u=_
  unfold childGate
  rw [whereAt]

variable {born : Births T key prec tw bw page}
variable {keys : PageKeys born} {rootTags : r.host.Row⊕r.host.Col→Origin key prec page}
variable (files : SiteFiles born keys rootTags) (rootPorts : Port r.host.Edge→Payload key prec page)
variable (rootGates)

def RootGateContinues {c : Call (PhysicalHost f ell)} (p : Path sel r c)
    (u : c.host.Row⊕c.host.Col) : Prop :=
  ∃ a : r.host.Row⊕r.host.Col, ∃ tr : Trace (point r.host a) (point c.host u),
    BodyFollows files rootPorts p u (point r.host a)
      (fun x=>(rootPorts x.val).2) (rootTags a) tr ∧
    gateHistory T rootGates p u=rootGates a

theorem linked_paths_carry_gate_and_body_together
    (L : Linked files rootPorts)
    (boot : ∀ (u : r.host.Row⊕r.host.Col) (h : PortAt (point r.host u)),(rootPorts h.val).1=rootTags u)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) :
    ∀ u : c.host.Row⊕c.host.Col,
      RootGateContinues rootGates files rootPorts p u ∨
        (NativeContinues files rootPorts p u ∧ gateHistory T rootGates p u=none) := by
  induction p with
  | root =>
    intro u
    exact Or.inl ⟨u,Trace.start,⟨rfl,fun h=>Prod.ext (boot u h) rfl⟩,rfl⟩
  | @step c p w ih =>
    intro u
    let v := p.ticket w
    cases H : childVertices T v u with
    | inl old =>
      have sameGate := gate_history_keeps (rootGates:=rootGates) p w u old H
      let E := selected_retained_chart T v u old H
      rcases ih old.val with outer|inside
      · obtain ⟨initial,tr,⟨tag,bodies⟩,kept⟩ := outer
        have made := carried_retention_publishes_correct_body L p w u old H
          (fun x=>(rootPorts x.val).2) tr (rootTags initial) tag bodies
        exact Or.inl ⟨initial,E.symm ▸ tr.keep (retainedMove T v old),made,sameGate.trans kept⟩
      · obtain ⟨inner,empty⟩ := inside
        obtain ⟨ca,anc,kSlot,k,on,tr,tag,bodies⟩ := inner
        let seed := originSeed (layout T (anc.ticket kSlot)) (axis T (anc.ticket kSlot)) (anc.ticket kSlot).groupAt k
        have made := carried_retention_publishes_correct_body L p w u old H
          seed tr (nativeOrigin (files anc kSlot) k) tag bodies
        exact Or.inr ⟨⟨ca,anc,kSlot,k,.inherited p w on,E.symm ▸ tr.keep (retainedMove T v old),made⟩,
          sameGate.trans empty⟩
    | inr k =>
      let E := selected_packet_chart T v u k H
      exact Or.inr ⟨⟨c,p,w,k,.youngest p w rfl,E.symm ▸ Trace.start,
        actual_new_page_publishes_correct_body L p w u k H⟩,
        gate_history_fresh (rootGates:=rootGates) p w u k H⟩

end
#print axioms gate_history_keeps
#print axioms gate_history_fresh
#print axioms linked_paths_carry_gate_and_body_together
end J6R54TerminalBoot
