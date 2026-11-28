import J6R33StatefulArithmeticPageProjection

/-! Pointwise link for the actual, independently indexed Page. The
stored occurrence's creator and birth precision are not inferred from
the page key, and selecting a different inner key cannot supply its
capsule. -/
namespace J6R33StatefulArithmeticPage
open scoped Polynomial
open AOracleMachineTime AOracleMachineTimeTape A1R10 A1R11 A1R12
open J6R21Ancestor J6R20Ancestor J6R18ChildWrite J6R19Retained J6R24MeteredRecursion J6R22Active
open P1DyadicGrid P11FullPacking J6R10Repack J6R11Blueprint J6R9PacketScopes
open J6R30ProducedGateRegistry J6R32StatefulArithmetic

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {Net : Network E A B}
variable {f : ℤ[X]} {q ell m M key prec tw bw page : ℕ}
variable (r : Stored key prec tw bw (PagedEnvelope f ell prec page))
local notation "a" => r.payload.shape.a
local notation "p" => r.payload.shape.p
local notation "w" => r.payload.shape.w
local notation "i" => r.payload.shape.i

set_option maxHeartbeats 7000000 in
theorem true_page_port
    (hf : f.Monic) (F : Frame f q) (hEll : 0<ell)
    (P : PhysicalPacking Net r.payload.shape.a G) {t : ℤ}
    (ht : t∈grid a) (ht0 : t≠0) (hv : padicValInt 2 t=(i).val)
    (oldFile : EntryFile f ell Net) (g : G) (k : Page a P.copies G)
    (ξ : Fin m≃Mode i p P.mask) (β : Mode i p P.mask→₀ℕ)
    (ms : Fin m→ModeInput a p i w) (hMode : ModeMeaning P i g k ξ β ms)
    (rs : List (RowsOf P i g k)) (hnR : rs.Nodup) (haR : ∀ r',r'∈rs)
    (cs : List (ColsOf P i g k)) (hnC : cs.Nodup) (haC : ∀ c',c'∈cs)
    (b : ℕ) (hw : 0<w) (hb : m+1≤2^b) (hCount : rs.length<2^w)
    (hCodes : ∀ j,(ms j).code=encodeBits b j.succ.val)
    (bank : PageBank f ell key prec tw bw page)
    (addr : J6R15ModeCost.Word key) (selector : J6R15ModeCost.Word page)
    (above : (locate addr bank.records).result=some r)
    (data : pageFields r) (here : (locate selector r.payload.pages).result=some data)
    (owner : addr=r.stamp.creator) (birth : r.payload.shape.birth=r.stamp.created)
    (realT : r.context.center=t) (realB : r.context.codeWidth.val=b)
    (hRows : data.rows=rs.map (fun row=>slotWord P row.val))
    (hCols : data.cols=cs.map (fun col=>slotWord P col.val))
    (hModes : data.modes=List.ofFn ms)
    {cur : Point f ell}
    (tr : Trace (generatedPoint P i ht0 hv (castBox r.payload.shape.algebra
      (uvRead r.payload.shape.pPos r.payload.shape.old ell data.probe)) oldFile β g k) cur)
    (ord : Fin M≃cur.host.Edge) (bits : Fin M→Bool) (ports : List (PortAt cur)) (hall : ∀ v,v∈ports)
    (wires : List WireRead)
    (realWires : wires=ports.map (fun u=>⟨tr.literal (originSeed P i g k) u,
      List.replicate (ord.symm (edge u.val)).val true⟩)) :
    let read := readPage hf F hEll addr selector tr.depth wires (List.ofFn bits) bank
    F.decode read.result=(entry cur).read hf q
      (assignment cur.host.network (bits∘ord.symm) cur.vertex) ∧
      r.stamp.created.val=(entry cur).created ∧
      read.steps≤gatherFee (tr.depth+a+2) M ports.length+(locate addr bank.records).steps+
        (locate selector r.payload.pages).steps+
        invokeFee a r.payload.shape.old.length ell p q (i).val w b tr.depth ports.length rs.length cs.length m
          r.payload.shape.pPos+invokeStampFee key prec tw bw+14 := by
  let ghost := projectionBank r data addr
  have hit : (locate addr ghost.records).result=some (onePage r data) :=
    congrArg Meter.result (projection_hit r data addr)
  obtain ⟨v,tag,fee⟩ := source_fetched_port (onePage r data) hf F hEll P ht ht0 hv oldFile g k ξ β ms
    hMode rs hnR haR cs hnC haC b hw hb hCount hCodes ghost addr hit owner birth realT realB
    hRows hCols hModes tr ord bits ports hall wires realWires
  have pair := exact_paged_read_lift hf F hEll addr selector tr.depth wires (List.ofFn bits) bank r
    above data here owner birth
  let actual := readPage hf F hEll addr selector tr.depth wires (List.ofFn bits) bank
  let model := (ReadCode.generated (m:=M) addr tr.depth wires).run hf F hEll ghost (List.ofFn bits)
  have R : actual.result=model.result := pair.1
  have A : actual.steps+refHeadFee key=model.steps+(locate addr bank.records).steps+
      (locate selector r.payload.pages).steps+4 := pair.2
  have H : (locate addr ghost.records).steps=refHeadFee key :=
    congrArg Meter.steps (projection_hit r data addr)
  have bound : model.steps≤gatherFee (tr.depth+a+2) M ports.length+(locate addr ghost.records).steps+
      invokeFee a r.payload.shape.old.length ell p q (i).val w b tr.depth ports.length rs.length cs.length m
        r.payload.shape.pPos+invokeStampFee key prec tw bw+10 := fee
  rw [H] at bound
  dsimp only
  change F.decode actual.result=_ ∧ _ ∧ actual.steps≤_
  exact ⟨(congrArg F.decode R).trans v,tag,by omega⟩

#print axioms true_page_port
end J6R33StatefulArithmeticPage
