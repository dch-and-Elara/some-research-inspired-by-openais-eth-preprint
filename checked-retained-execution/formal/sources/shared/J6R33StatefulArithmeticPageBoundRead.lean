import J6R33StatefulArithmeticPagePhysical
import J6R33StatefulArithmeticPagePath
import J6R33StatefulArithmeticPageLeaf

/-! The proof uses exactly the atlas of a live ancestor occurrence;
its real page is a separate lookup within that immutable atlas. -/
namespace J6R33StatefulArithmeticPage
open scoped Polynomial
open AOracleMachineTime AOracleMachineTimeTape A1R10 A1R11 A1R12
open J6R21Ancestor J6R20Ancestor J6R18ChildWrite J6R19Retained J6R24MeteredRecursion J6R22Active
open P1DyadicGrid P11FullPacking J6R10Repack J6R11Blueprint J6R9PacketScopes
open J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R12Blueprint J1PPrinted

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
variable {ticket : J6R26DescriptorTree.Ticket sel r}
variable (Q : J6R33StatefulArithmeticPage.Birth T ticket key prec tw bw page)

set_option maxHeartbeats 6500000 in
theorem actual_inherited_page_port
    {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
    {Net : Network E A B} {q m M : ℕ}
    (F : Frame f q) (hEll : 0<ell)
    (P : PhysicalPacking Net Q.shape.a G) {t : ℤ}
    (ht : t∈grid Q.shape.a) (ht0 : t≠0) (hv : padicValInt 2 t=Q.shape.i.val)
    (oldFile : EntryFile f ell Net) (g : G) (k : Page Q.shape.a P.copies G)
    (ξ : Fin m≃Mode Q.shape.i Q.shape.p P.mask) (β : Mode Q.shape.i Q.shape.p P.mask→₀ℕ)
    (ms : Fin m→ModeInput Q.shape.a Q.shape.p Q.shape.i Q.shape.w) (hMode : ModeMeaning P Q.shape.i g k ξ β ms)
    (rs : List (RowsOf P Q.shape.i g k)) (hnR : rs.Nodup) (haR : ∀ row,row∈rs)
    (cs : List (ColsOf P Q.shape.i g k)) (hnC : cs.Nodup) (haC : ∀ col,col∈cs)
    (b : ℕ) (hw : 0<Q.shape.w) (hb : m+1≤2^b) (hCount : rs.length<2^Q.shape.w)
    (hCodes : ∀ j,(ms j).code=encodeBits b j.succ.val)
    (bank : PageBank f ell key prec tw bw page)
    (born : J6R33StatefulArithmeticPage.Births T key prec tw bw page)
    {c : Call (PhysicalHost f ell)} (path : Path sel r c)
    (wasBorn : OnPath born Q.job path) (rootLive : PageBank f ell key prec tw bw page→Prop)
    (live : opened born rootLive path bank)
    (pg : J6R15ModeCost.Word page)
    (data : OriginFields Q.shape.a Q.shape.p ell Q.shape.w Q.shape.old Q.shape.i)
    (hit : (locate pg Q.rows).result=some data)
    (realT : Q.ctx.center=t) (realB : Q.ctx.codeWidth.val=b)
    (hRows : data.rows=rs.map (fun row=>slotWord P row.val))
    (hCols : data.cols=cs.map (fun col=>slotWord P col.val))
    (hModes : data.modes=List.ofFn ms)
    {cur : Point f ell}
    (tr : Trace (generatedPoint P Q.shape.i ht0 hv
      (castBox Q.shape.algebra (uvRead Q.shape.pPos Q.shape.old ell data.probe)) oldFile β g k) cur)
    (ord : Fin M≃cur.host.Edge) (bits : Fin M→Bool) (ports : List (PortAt cur)) (hall : ∀ v,v∈ports)
    (wires : List WireRead)
    (realWires : wires=ports.map (fun u=>⟨tr.literal (originSeed P Q.shape.i g k) u,
      List.replicate (ord.symm (edge u.val)).val true⟩)) :
    let op := (PageReadCode.generated (edges:=M) Q.job.identifier pg tr.depth wires).run hf F hEll bank
      (List.ofFn bits)
    F.decode op.result=(entry cur).read hf q
      (assignment cur.host.network (bits∘ord.symm) cur.vertex) ∧
      (entry cur).created=ticket.child.prec ∧
      op.steps≤gatherFee (tr.depth+Q.shape.a+2) M ports.length+(locate Q.job.identifier bank.records).steps+
        (locate pg Q.rows).steps+
        invokeFee Q.shape.a Q.shape.old.length ell Q.shape.p q Q.shape.i.val Q.shape.w b tr.depth
          ports.length rs.length cs.length m Q.shape.pPos+invokeStampFee key prec tw bw+14 := by
  have found := (ancestor_paged_live born Q.job path wasBorn bank live).2
  obtain ⟨value,tag,fee⟩ := true_page_port Q.job.immutable.payload hf F hEll P ht ht0 hv oldFile
    g k ξ β ms hMode rs hnR haR cs hnC haC b hw hb hCount hCodes bank Q.job.identifier pg found
    data hit rfl rfl realT realB hRows hCols hModes tr ord bits ports hall wires realWires
  exact ⟨value,tag.symm.trans Q.tag.2,fee⟩

#print axioms actual_inherited_page_port
end J6R33StatefulArithmeticPage
