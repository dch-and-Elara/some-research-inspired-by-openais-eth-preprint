
import J6R30ProducedGateRegistryNative
import J6R30ProducedGateRegistryPhysicalUse

/-! The physical pointwise theorem is applied to the *returned*
directory, with the immutable capsule produced by the same R27
frame compiler. It splits exact writer/read charges without reducing
or duplicating the actual schedule representation. -/
namespace J6R30ProducedGateRegistry
open scoped Polynomial
open AOracleMachineTime AOracleMachineTimeTape A1R10 A1R11 A1R12
open J6R21Ancestor J6R20Ancestor J6R18ChildWrite J6R19Retained
open P1DyadicGrid P11FullPacking J6R10Repack J6R11Blueprint J6R9PacketScopes

variable {E A B G : Type} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {Net : Network E A B}

set_option maxHeartbeats 4400000 in
theorem registered_physical_port_run {f : ℤ[X]} {p q ell w m M key prec tw bw codew pagew : ℕ}
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
    (bank : GateLedger (ell:=ell) (w:=w) old i key prec tw bw) (sync : bank.synced)
    (made : Meter (DirRow key)) (offset : ℕ) (ctx : CentreContext tw bw)
    (realT : ctx.center=t) (realB : ctx.codeWidth.val=b)
    (frames : Frames old a w codew pagew) (fit : i.val+1≤w)
    (born : J6R15ModeCost.Word prec) (realP : born.val=p)
    (parsed : loadAt prec offset made.result.bytes=⟨some born,headerReadFee prec offset⟩)
    (fresh : ∀ r∈bank.headers,r.id≠made.result.id)
    (F : OriginFields a p ell w old i) (compiled : (frames.compile hp hEll fit).result=some F)
    (hRows : F.rows=rs.map (fun r=>slotWord P r.val))
    (hCols : F.cols=cs.map (fun c=>slotWord P c.val)) (hModes : F.modes=List.ofFn ms)
    {cur : Point f ell}
    (tr : Trace (generatedPoint P i ht0 hv (castBox hO (uvRead hp old ell F.probe)) oldFile β g k) cur)
    (ord : Fin M≃cur.host.Edge) (bits : Fin M→Bool) (ports : List (PortAt cur)) (hall : ∀ u,u∈ports)
    (wires : List WireRead)
    (realWires : wires=ports.map (fun u=>⟨tr.literal (originSeed P i g k) u,
      List.replicate (ord.symm (edge u.val)).val true⟩)) :
    let hD := (size_of_monic_words hp hf hO).trans (size_of_monic_words hq hf hN).symm
    let published := publishFrames bank made offset ctx frames hp hEll fit
    let out := gatherAndInvoke (new:=new) hp he hEll hD made.result.id born tr.depth wires
      (List.ofFn bits) published.result.1
    let stored := publishedRow made.result born ctx F
    ∃ word, out.result=some word ∧
      castBox hN (uvRead hq new ell word)=(entry cur).read hf q
        (assignment cur.host.network (bits∘ord.symm) cur.vertex) ∧
      stored.payload.stamp.created.val=(entry cur).created ∧
      published.result.1.records=stored::bank.records ∧ published.result.2=true ∧
      published.steps=publishFee bank made offset (frames.compile hp hEll fit) ∧
      out.steps≤gatherFee (tr.depth+a+2) M ports.length+refHeadFee key+
        invokeFee a old.length ell p q i.val w b tr.depth ports.length rs.length cs.length m hp+
        invokeStampFee key prec tw bw+8 := by
  let hD := (size_of_monic_words hp hf hO).trans (size_of_monic_words hq hf hN).symm
  let written := publishFrames bank made offset ctx frames hp hEll fit
  let stored := publishedRow made.result born ctx F
  let next : GateLedger (ell:=ell) (w:=w) old i key prec tw bw :=
    ⟨made.result::bank.headers,stored::bank.records⟩
  have pub : written=⟨(next,true),publishFee bank made offset (frames.compile hp hEll fit)⟩ :=
    publish_compiled_exact bank sync made offset ctx (frames.compile hp hEll fit) F compiled
      born parsed fresh
  have head : locate made.result.id next.records=⟨some stored.payload,refHeadFee key⟩ :=
    ref_head_exact stored bank.records
  have hit : (locate made.result.id next.records).result=some stored.payload := by rw [head]
  obtain ⟨word,returned,semantic,tag,fee⟩ :=
    real_lookup_consumes_source hf heF hp hq hO hN he hEll P i ht ht0 hv oldFile g k ξ β ms
      hMode rs hnR haR cs hnC haC b hw hb hCount hCodes next made.result.id stored.payload hit
      rfl realP realT realB hRows hCols hModes tr ord bits ports hall wires realWires
  dsimp only
  change ∃ word, (gatherAndInvoke (new:=new) hp he hEll hD made.result.id born tr.depth
      wires (List.ofFn bits) written.result.1).result=some word ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  rw [pub]
  refine ⟨word,returned,semantic,tag,congrArg (fun m=>m.result.1.records) pub,congrArg (fun m=>m.result.2) pub,congrArg Meter.steps pub,?_⟩
  rw [head] at fee
  change (gatherAndInvoke (new:=new) hp he hEll hD made.result.id born tr.depth
    wires (List.ofFn bits) written.result.1).steps≤_
  rw [pub]
  exact fee

#print axioms registered_physical_port_run
end J6R30ProducedGateRegistry




