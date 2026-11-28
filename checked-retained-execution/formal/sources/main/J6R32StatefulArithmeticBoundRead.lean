import J6R32StatefulArithmeticReadPhysical

/-! Binding leaf code to one actually issued ancestor. Its identity
uses a Type-valued occurrence path, not equality of numerical calls.
An arbitrary fetched coefficient cannot satisfy this ABI by fiat:
the runtime is the original or generated gate program. -/
namespace J6R32StatefulArithmetic
open scoped Polynomial
open AOracleMachineTime AOracleMachineTimeTape A1R10 A1R11 A1R12
open J6R21Ancestor J6R20Ancestor J6R18ChildWrite J6R19Retained J6R24MeteredRecursion J6R22Active
open P1DyadicGrid P11FullPacking J6R10Repack J6R11Blueprint J6R9PacketScopes
open J6R30ProducedGateRegistry
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R12Blueprint J1PPrinted

section Ancestry
variable {f : ℤ[X]} {ell s C key prec tw bw : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
variable (births : Births T key prec tw bw)

inductive Contains (j : GJob f ell key prec tw bw) :
    ∀ {c : Call (PhysicalHost f ell)},Path sel r c→Prop where
  | latest {c} (p : Path sel r c) (w : (Plan sel).Slot c) (same : (births p w).job=j) :
      Contains j (.step p w)
  | ancestor {c} (p : Path sel r c) (w : (Plan sel).Slot c) (older : Contains j p) :
      Contains j (.step p w)

theorem live_from_path (j : GJob f ell key prec tw bw)
    {rootLive : AnyLedger f ell key prec tw bw→Prop}
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (uses : Contains births j p)
    (B : AnyLedger f ell key prec tw bw) (state : Ancestors births rootLive p B) : IsLive j B := by
  induction uses with
  | latest p w eq =>
    change Ancestors births rootLive p B ∧ IsLive (births p w).job B at state
    exact eq ▸ state.2
  | ancestor p w older ih =>
    change Ancestors births rootLive p B ∧ IsLive (births p w).job B at state
    exact ih state.1

variable {ticket : J6R26DescriptorTree.Ticket sel r}
variable (Q : Birth T ticket key prec tw bw)

set_option maxHeartbeats 5500000 in
theorem registered_ancestor_port
    {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
    {Net : Network E A B} {q m M : ℕ}
    (F : Frame f q) (hEll : 0<ell)
    (P : PhysicalPacking Net Q.shape.a G) {t : ℤ}
    (ht : t∈grid Q.shape.a) (ht0 : t≠0) (hv : padicValInt 2 t=Q.shape.i.val)
    (oldFile : EntryFile f ell Net) (g : G) (k : Page Q.shape.a P.copies G)
    (ξ : Fin m≃Mode Q.shape.i Q.shape.p P.mask) (β : Mode Q.shape.i Q.shape.p P.mask→₀ℕ)
    (ms : Fin m→ModeInput Q.shape.a Q.shape.p Q.shape.i Q.shape.w) (hMode : ModeMeaning P Q.shape.i g k ξ β ms)
    (rs : List (RowsOf P Q.shape.i g k)) (hnR : rs.Nodup) (haR : ∀ r',r'∈rs)
    (cs : List (ColsOf P Q.shape.i g k)) (hnC : cs.Nodup) (haC : ∀ c',c'∈cs)
    (b : ℕ) (hw : 0<Q.shape.w) (hb : m+1≤2^b) (hCount : rs.length<2^Q.shape.w)
    (hCodes : ∀ j,(ms j).code=encodeBits b j.succ.val)
    (bank : AnyLedger f ell key prec tw bw)
    (live : IsLive Q.job bank)
    (realT : Q.context.center=t) (realB : Q.context.codeWidth.val=b)
    (hRows : Q.fields.rows=rs.map (fun row=>slotWord P row.val))
    (hCols : Q.fields.cols=cs.map (fun col=>slotWord P col.val))
    (hModes : Q.fields.modes=List.ofFn ms)
    {cur : Point f ell}
    (tr : Trace (generatedPoint P Q.shape.i ht0 hv
      (castBox Q.shape.algebra (uvRead Q.shape.pPos Q.shape.old ell Q.fields.probe)) oldFile β g k) cur)
    (ord : Fin M≃cur.host.Edge) (bits : Fin M→Bool) (ports : List (PortAt cur)) (hall : ∀ v,v∈ports)
    (wires : List WireRead)
    (realWires : wires=ports.map (fun u=>⟨tr.literal (originSeed P Q.shape.i g k) u,
      List.replicate (ord.symm (edge u.val)).val true⟩)) :
    let read := (ReadCode.generated (m:=M) Q.job.identifier tr.depth wires).run hf F hEll bank (List.ofFn bits)
    F.decode read.result=(entry cur).read hf q
      (assignment cur.host.network (bits∘ord.symm) cur.vertex) ∧
      (entry cur).created=ticket.child.prec ∧
      read.steps≤gatherFee (tr.depth+Q.shape.a+2) M ports.length+(locate Q.job.identifier bank.records).steps+
        invokeFee Q.shape.a Q.shape.old.length ell Q.shape.p q Q.shape.i.val Q.shape.w b tr.depth
          ports.length rs.length cs.length m Q.shape.pPos+invokeStampFee key prec tw bw+10 := by
  obtain ⟨value,tag,fee⟩ := source_fetched_port Q.job.immutable.payload hf F hEll P ht ht0 hv oldFile
    g k ξ β ms hMode rs hnR haR cs hnC haC b hw hb hCount hCodes bank Q.job.identifier live.2
    rfl rfl realT realB hRows hCols hModes tr ord bits ports hall wires realWires
  exact ⟨value,tag.symm.trans (issued_prec_and_key Q).2,fee⟩
end Ancestry

section Original
open J6OrientedHost J6R21Leaf
variable {S V : Type} [LinearOrder S] [Fintype S] [Fintype V]

theorem original_port_code {f : ℤ[X]} {ell created current m l q M width key prec tw bw : ℕ}
    (T : Plant V m q) (w : Fin (J6Mesh.a m)→S) (hf : f.Monic)
    (hp : 0<created) (F : Frame f current) (hEll : 0<ell)
    (v : PlantNode (b:=J6Mesh.K m) (l:=l) T w)
    {cur : Point f ell} (tr : Trace (actualOriginalPoint (created:=created) T w v) cur)
    (ord : Fin M≃cur.host.Edge) (fit : M≤2^width)
    (A : OriginalGateTape M width)
    (design : A=gateTape fit (tracedSlot tr ord ∘ (originalPortGate T w v).port)
      (originalPortGate T w v).gate)
    (bits : Fin M→Bool) (bank : AnyLedger f ell key prec tw bw) :
    let op := (ReadCode.original (key:=key) width A).run hf F hEll bank (List.ofFn bits)
    F.decode op.result=(entry cur).read hf current
      (assignment cur.host.network (bits∘ord.symm) cur.vertex) ∧
      (entry cur).created=created ∧
      op.steps≤originalGateFee M width (originalPortGate T w v).degree+uvWidth F.words.length ell current+4 := by
  have he : 0<f.natDegree := F.natDegree hf ▸ F.sizePos
  obtain ⟨out,tag,fee⟩ := original_through_trace T w hf hp F.hp he hEll F.sizePos F.exactMod
    v tr ord fit A design bits
  exact ⟨(boxTransport_cast F.exactMod _).trans out,tag,fee⟩
end Original

#print axioms live_from_path
#print axioms registered_ancestor_port
#print axioms original_port_code
end J6R32StatefulArithmetic
