
import J6R30ProducedGateRegistryInvoke
import J6R21AncestorOriginReads

/-! Pointwise equality of an actual retained-entry request to the
source file at the receiving precision. The successful lookup is the
only place the executor gets its fields, site values and birth stamp.
The footprint and physical mode receipts are those supplied by R27. -/
namespace J6R30ProducedGateRegistry
open scoped Polynomial
open AOracleMachineTime AOracleMachineTimeTape A1R10 A1R11 A1R12
open J6R21Ancestor J6R20Ancestor J6R18ChildWrite J6R19Retained
open P1DyadicGrid P11FullPacking J6R10Repack J6R11Blueprint J6R9PacketScopes

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {Net : Network E A B}

set_option maxHeartbeats 4200000 in
theorem real_lookup_consumes_source {f : ℤ[X]} {p q ell w m M key prec tw bw : ℕ}
    (hf : f.Monic) (heF : 0<f.natDegree) (hp : 0<p) (hq : 0<q)
    {old : List (A1R10.Word p)} {new : List (A1R10.Word q)}
    (hO : Modulus p hp old=NativeProbeRing.liftPoly p f)
    (hN : Modulus q hq new=NativeProbeRing.liftPoly q f)
    (he : 0<old.length) (hEll : 0<ell)
    (P : PhysicalPacking Net a G) (i : Fin a) {t : ℤ}
    (ht : t∈grid a) (ht0 : t≠0) (hv : padicValInt 2 t=i.val)
    (oldFile : EntryFile f ell Net) (g : G) (k : Page a P.copies G)
    (ξ : Fin m≃Mode i p P.mask) (β : Mode i p P.mask→₀ℕ)
    (ms : Fin m→ModeInput a p i w) (hMode : ModeMeaning P i g k ξ β ms)
    (rs : List (RowsOf P i g k)) (hnR : rs.Nodup) (haR : ∀ r,r∈rs)
    (cs : List (ColsOf P i g k)) (hnC : cs.Nodup) (haC : ∀ c,c∈cs)
    (b : ℕ) (hw : 0<w) (hb : m+1≤2^b) (hCount : rs.length<2^w)
    (hCodes : ∀ j,(ms j).code=encodeBits b j.succ.val)
    (bank : GateLedger (ell:=ell) (w:=w) old i key prec tw bw)
    (addr : J6R15ModeCost.Word key)
    (rec : Stored key prec tw bw (OriginFields a p ell w old i))
    (located : (locate addr bank.records).result=some rec)
    (owner : addr=rec.stamp.creator) (birth : rec.stamp.created.val=p)
    (realT : rec.context.center=t) (realB : rec.context.codeWidth.val=b)
    (hRows : rec.payload.rows=rs.map (fun r=>slotWord P r.val))
    (hCols : rec.payload.cols=cs.map (fun c=>slotWord P c.val))
    (hModes : rec.payload.modes=List.ofFn ms)
    {cur : Point f ell}
    (tr : Trace (generatedPoint P i ht0 hv (castBox hO (uvRead hp old ell rec.payload.probe))
      oldFile β g k) cur)
    (ord : Fin M≃cur.host.Edge) (bits : Fin M→Bool) (ports : List (PortAt cur)) (hall : ∀ u,u∈ports)
    (wires : List WireRead)
    (realWires : wires=ports.map (fun u=>⟨tr.literal (originSeed P i g k) u,
      List.replicate (ord.symm (edge u.val)).val true⟩)) :
    let hD := (size_of_monic_words hp hf hO).trans (size_of_monic_words hq hf hN).symm
    let op := gatherAndInvoke (new:=new) hp he hEll hD addr rec.stamp.created tr.depth wires (List.ofFn bits) bank
    ∃ word, op.result=some word ∧
      castBox hN (uvRead hq new ell word)=(entry cur).read hf q
        (assignment cur.host.network (bits∘ord.symm) cur.vertex) ∧
      rec.stamp.created.val=(entry cur).created ∧
      op.steps≤gatherFee (tr.depth+a+2) M ports.length+(locate addr bank.records).steps+
        invokeFee a old.length ell p q i.val w b tr.depth ports.length rs.length cs.length m hp+
        invokeStampFee key prec tw bw+8 := by
  let hD := (size_of_monic_words hp hf hO).trans (size_of_monic_words hq hf hN).symm
  let raw := gather (tr.depth+a+2) wires (List.ofFn bits)
  let localKey := tr.literal (originSeed P i g k)
  let lane (u : PortAt cur) := ord.symm (edge u.val)
  have width (u : PortAt cur) : (localKey u).length=tr.depth+a+2 := by
    apply literal_address_width tr
    intro z
    simp only [originSeed,List.length_cons,(originKey P i g k z).slot.size]
  obtain ⟨rawValue,rawFee⟩ := gather_ordinals bits ports localKey lane _ (fun u _=>width u) wires realWires
  let readBits := assignment cur.host.network (bits∘ord.symm) cur.vertex
  have rawWord : raw.result=ports.map (fun u=>(localKey u,readBits u)) := rawValue
  let ev := invokeTrace (new:=new) hp he hEll hD rec.payload.probe t i b tr.depth
    rec.payload.rows rec.payload.cols (List.ofFn ms) raw.result
  obtain ⟨ans,tag,paid⟩ := invoke_history_native hf heF hp hq hO hN he hEll
    P i ht ht0 hv rec.payload.probe oldFile g k ξ β ms hMode rs hnR haR cs hnC haC b hw hb hCount hCodes
    tr readBits ports hall raw.result rawWord rec.payload.rows rec.payload.cols hRows hCols
  have hit := fetch_executes_record (new:=new) hp he hEll hD addr rec.stamp.created tr.depth
    raw.result bank rec located owner rfl
  dsimp only at hit
  rw [realT,realB,hModes] at hit
  change invokeFromBank (new:=new) hp he hEll hD addr rec.stamp.created tr.depth raw.result bank=
    ⟨some ev.result,(locate addr bank.records).steps+ev.steps+invokeStampFee key prec tw bw+4⟩ at hit
  dsimp only
  unfold gatherAndInvoke
  dsimp only
  rw [hit]
  refine ⟨ev.result,rfl,ans,birth.trans tag.symm,?_⟩
  change raw.steps+((locate addr bank.records).steps+ev.steps+invokeStampFee key prec tw bw+4)+4≤_
  change raw.steps≤_ at rawFee
  change ev.steps≤_ at paid
  omega

#print axioms real_lookup_consumes_source
end J6R30ProducedGateRegistry

