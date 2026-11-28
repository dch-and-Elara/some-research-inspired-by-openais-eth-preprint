import J6R52TerminalFreshSemantics
import J6R49SourceLayoutFrames

/-! The born packet point is the right column of this exact physical
child, with its actual chosen edge key order. Transport is a
specification proof and does not recode any runtime bits. -/
namespace J6R52Terminal
open scoped Polynomial
open Polynomial AOracleMachineTime J6ActiveRun J6R9Recursive J6R10Repack
open J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R26DescriptorTree J6R24MeteredRecursion J6R21Ancestor J6R22Active
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R34ChildPath J6R49SourceLayout J6R50Leaf J6R50SourceProducer
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 20000000
set_option maxRecDepth 3700
set_option Elab.async false

theorem literal_column_value_transport {f : ℤ[X]} {ell p M : ℕ} (hf : f.Monic)
    (H K : PhysicalHost f ell) (same : H=K) (col : H.Col)
    (ord : Fin M≃H.Edge) (bits : Fin M→Bool) :
    let idx := (Equiv.cast (congrArg PhysicalHost.Col same)) col
    let v := (Sum.inr idx : K.Row⊕K.Col)
    let o := ord.trans (Equiv.cast (congrArg PhysicalHost.Edge same))
    (K.file v).read hf p (assignment K.network (bits∘o.symm) v)=
      (H.file (.inr col)).read hf p (assignment H.network (bits∘ord.symm) (.inr col)) := by
  subst K
  rfl

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {ticket : Ticket sel r}

theorem emitted_fresh_word_is_actual_child_column
    (site : StoredSite T ticket key prec tw bw page) (col : ticket.child.host.Col)
    {c : Call (PhysicalHost f ell)} (path : Path sel r c)
    (born : J6R33StatefulArithmeticPage.Births T key prec tw bw page)
    (wasBorn : OnPath born site.birth.job path)
    (rootLive : PageBank f ell key prec tw bw page→Prop)
    (B : PageBank f ell key prec tw bw page) (live : opened born rootLive path B)
    (F : Frame f ticket.child.prec) (bits : Fin ticket.child.edges→Bool) :
    let k := physicalChildCols (T:=T) (v:=ticket) col
    let ord := actualEdgeOrder T ticket site.birth.native.physical
    F.decode ((freshWord site k).read hf F T.vPositive B (List.ofFn bits)).result=
      (ticket.child.host.file (.inr col)).read hf ticket.child.prec
        (assignment ticket.child.host.network (bits∘ord.symm) (.inr col)) := by
  let k := physicalChildCols (T:=T) (v:=ticket) col
  let ord := actualEdgeOrder T ticket site.birth.native.physical
  have a := emitted_fresh_word_reads_actual_page site k path born wasBorn rootLive B live F bits
  have b := literal_column_value_transport (p:=ticket.child.prec) hf ticket.child.host
    (literalHost T ticket) (actual_ticket_host T ticket) col ord bits
  exact a.trans b

end
#print axioms literal_column_value_transport
#print axioms emitted_fresh_word_is_actual_child_column
end J6R52Terminal
