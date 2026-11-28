
import J6R32RootGeneratedRegistryInputsPublish
import J6R32RootGeneratedRegistryInputsHeader
import J6R32RootGeneratedRegistryInputsTypedPorts
import J6R26StablePreparedRootGeometry
import J6R28GeneratedRootFrameLiteral

/-! The fixed odd J6 root's actual owner selector, precision and probe
bank are the occurrence used by the publication. The exterior header
is separate from a native-prefix Ticket; the latter is not synthesized.
The actual stable root half-port file is made from the same signed literal tape. -/
namespace J6R32RootGeneratedRegistryInputs
open scoped Classical Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape
open J6Mesh J6OrientedHost P11FullPacking J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R27PrescribedProbe J6R27OriginalGate J6R30GeneratedRootLayout J6R31RootResidentTables
open J6R17ModeTape J6R18ChildWrite J6R20Ancestor J6R16ModeCost
open J6R15ModeCost J6R12Repack J6R11Repack J6R10Repack J6R12Blueprint J6R11Blueprint J6R26DescriptorTree
open J6ActiveRun J6ActiveSchedule J1PPrinted J6R25PreparedSupply J6R21Ancestor J6R30ProducedGateRegistry
set_option maxHeartbeats 24000000
set_option maxRecDepth 2600
set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T (J6R28GeneratedRootFrame.constantRootWord m))

noncomputable def stableRootRegistration
    {edgew tc tj key prec tw bw r c d q : ℕ}
    (ell : ℕ) (positive : 0<ell) (hf : f.Monic) (field : Meter (Frame f (J6SourcePrecision.printed m base)))
    (atCenter : J6Recovery.Addr m)
    (z : Fin (externalProbeDegree (physicalSize m native) (physicalRootCall f ell base m (printedHalf m) n T (J6R28GeneratedRootFrame.constantRootWord m))+1))
    (source : LiteralPortFile T r c d)
    (hq : 0<q) (hQ : 1≤q) (copies pre : Word q)
    (A : ExternalAddress tc tj (pageKeyWidth m)) (issue : Meter (Word key)) (birth : Word prec) (truth : birth.val=(J6SourcePrecision.printed m base))
    (query : QueryKey m q) (codew : ℕ) (ctx : CentreContext tw bw)
    (resident : AnyLedger f ell key prec tw bw) :
    Meter (AnyLedger f ell key prec tw bw×Bool) :=
  let bank := buildRootBitBank G ell
  let P := makeTypedRootParent G source ell atCenter
  let entry := (externalHeaderJob (b:=edgew) A birth (word (q:=1) 0) P.result.raw).make issue
  let input := makeOuterFrames field.result hf bank.result m hq (oddAxis m) copies pre
    source.raw query z codew
  let result := publishOuterFrames field.result (oddAxis m) positive hQ birth truth
    entry (externalAddrWidth tc tj (pageKeyWidth m)) ctx resident input
  ⟨result.result,field.steps+bank.steps+P.steps+result.steps+4⟩

theorem register_literal_odd_root
    {edgew tc tj key prec tw bw r c d q : ℕ}
    (ell : ℕ) (positive : 0<ell) (hf : f.Monic) (field : Meter (Frame f (J6SourcePrecision.printed m base)))
    (atCenter : J6Recovery.Addr m)
    (z : Fin (externalProbeDegree (physicalSize m native) (physicalRootCall f ell base m (printedHalf m) n T (J6R28GeneratedRootFrame.constantRootWord m))+1))
    (source : LiteralPortFile T r c d)
    (hq : 0<q) (hQ : 1<q) (copies pre : Word q) (copiesOK : copies.val=K m) (preOK : pre.val=(J6SourcePrecision.printed m base))
    (page : Page (a m) (K m) (Fin 64)) (g : Fin 64)
    (A : ExternalAddress tc tj (pageKeyWidth m)) (centerOK : A.center.val=index m atCenter)
    (sampleOK : A.sample.val=z.val) (groupOK : A.group.val=g.val)
    (pageOK : A.page=residentPageKey m page)
    (issue : Meter (Word key)) (birth : Word prec) (pOK : birth.val=(J6SourcePrecision.printed m base))
    (edgePos : 0<edgew) (edgeOK : (exteriorChild G ell atCenter z g).edges<2^edgew)
    (query : QueryKey m q) (queryOK : query.matches page g)
    (codew : ℕ) (codePos : 0<codew)
    (codeOK : 1+(writeResidents m hq (oddAxis m) copies pre source.raw).result.roster.modes.length<2^codew)
    (ctx : CentreContext tw bw)
    (sameCentre : ctx.center=(index m atCenter:ℤ)) (sameCode : ctx.codeWidth.val=codew)
    (resident : AnyLedger f ell key prec tw bw) (sync : resident.synced)
    (fresh : ∀ row∈resident.headers,row.id≠issue.result) :
    let P := makeTypedRootParent G source ell atCenter
    let Z := stableRootRegistration (edgew:=edgew) G ell positive hf field atCenter z source
      hq hQ.le copies pre A issue birth pOK query codew ctx resident
    let entry := (externalHeaderJob (b:=edgew) A birth (word (q:=1) 0) P.result.raw).make issue
    let child := exteriorChild G ell atCenter z g
    let Dg := externalProbeDegree (physicalSize m native) (physicalRootCall f ell base m (printedHalf m) n T (J6R28GeneratedRootFrame.constantRootWord m))
    let shape := exteriorShape (q:=q) field.result (oddAxis m) birth pOK
    let P0 := rootChart T
    ∃ fields : OriginFields (a m) (J6SourcePrecision.printed m base) ell q field.result.words (oddAxis m), ∃ N : ℕ,
      ∃ ξ : Fin N ≃ PacketMode (oddAxis m) (K m) (2^((oddAxis m).val+1)) (J6SourcePrecision.printed m base),
        ∃ ms : Fin N → ModeInput (a m) (J6SourcePrecision.printed m base) (oddAxis m) q,
      let row := publishedRow entry.result birth ctx (⟨shape,fields⟩ : Envelope f ell prec)
      Z.result.2=true ∧ Z.result.1.synced ∧
        locate issue.result Z.result.1.records=⟨some row.payload,refHeadFee key⟩ ∧
        Z.result.1.records=row::resident.records ∧
        row.payload.checkedHeader=A.bytes++childHeaderBytes birth (word (q:=1) child.depth)
          (word (q:=edgew) child.edges) ((P.result.physicalSelected g).map P.result.record |>.flatMap rowBytes) ∧
        row.payload.stamp.created.val=child.prec ∧
        row.payload.context.center=(G.centre ell atCenter).val ∧ row.payload.context.codeWidth.val=codew ∧
        A.page=residentPageKey m page ∧
        fields.rows=(sourceRows P0 (oddAxis m) g page (actualWires m)).map (fun u=>slotWord P0 u.val) ∧
        fields.cols=(sourceCols P0 (oddAxis m) g page (actualWires m)).map (fun u=>slotWord P0 u.val) ∧
        fields.modes=List.ofFn ms ∧
        ModeMeaning P0 (oddAxis m) g page (ξ.trans (packet_mode_equiv P0.mask (oddAxis m)
          (J6SourcePrecision.printed m base)).symm) 0 ms ∧
        (∀ u,(ms u).code=encodeBits codew u.succ.val) ∧
        J6R22Active.boxTransport field.result.exactMod
          (A1R10.uvRead field.result.hp field.result.words ell fields.probe)=
            J6R14ZeroMode.prescribedNode (rootPreset G ell) (J6SourcePrecision.printed m base) ell z ∧
        Z.steps≤field.steps+(positiveTapeFee f.natDegree (Dg+1)+3)+halfTapeFee m r c d+
          (residentsFee m q 0 (J6SourcePrecision.printed m base) r c d+(Dg+1)*(f.natDegree+2)+3*codew+12)+
          publicationOverhead resident entry (externalAddrWidth tc tj (pageKeyWidth m))+
          framePayloadFee (J6SourcePrecision.printed m base) ell field.result.words.length (a m) 0 q codew
            (pageKeyWidth m) (M m) N (D m*K m)+shapeFrameFee prec+8 := by
  let B := buildRootBitBank G ell
  let P := makeTypedRootParent G source ell atCenter
  let Dg := externalProbeDegree (physicalSize m native) (physicalRootCall f ell base m (printedHalf m) n T (J6R28GeneratedRootFrame.constantRootWord m))
  let entry := (externalHeaderJob (b:=edgew) A birth (word (q:=1) 0) P.result.raw).make issue
  let child := exteriorChild G ell atCenter z g
  let shape := exteriorShape (q:=q) field.result (oddAxis m) birth pOK
  let prep := makeOuterFrames field.result hf B.result m hq (oddAxis m) copies pre source.raw query z codew
  let pub := publishOuterFrames field.result (oddAxis m) positive hQ.le birth pOK entry (externalAddrWidth tc tj (pageKeyWidth m)) ctx resident prep
  have hg := odd_site_matches_geometry G ell atCenter
  have hC : (A.center.val:ℤ)=(G.centre ell atCenter).val := by rw [centerOK,hg.2.2.1]
  have hh : birth.val=registerPrecision (rootParams f ell m native)
      (physicalRootCall f ell base m (printedHalf m) n T (J6R28GeneratedRootFrame.constantRootWord m)) (G.centre ell atCenter) :=
    pOK.trans (G.precision ell atCenter).symm
  have addr0 : (word (q:=1) 0).val=(physicalRootCall f ell base m (printedHalf m) n T (J6R28GeneratedRootFrame.constantRootWord m)).depth :=
    word_val (by decide)
  have depthOK : (physicalRootCall f ell base m (printedHalf m) n T
      (J6R28GeneratedRootFrame.constantRootWord m)).depth+1<2^1 :=
    show (1:ℕ)<2 by decide
  obtain ⟨id,bytes,parsed,trueBirth,_,_,_⟩ := make_external_header_exact (G.selector ell) (G.ready ell)
    (G.centre ell atCenter) (b:=edgew) P.result (rootPreset G ell) z g A hC sampleOK groupOK issue
    birth hh (word (q:=1) 0) addr0 (by decide) depthOK edgePos edgeOK
  obtain ⟨out,N,ξ,ms,built,probe,rs,cs,roster,sem,codes,prepFee,compFee⟩ :=
    root_prescribed_frames_exact source field.result hf positive B.result z hq (oddAxis m) hQ copies pre
      copiesOK preOK page g query queryOK codew codePos codeOK
  have clean : ∀ row∈resident.headers,row.id≠entry.result.id := by
    change entry.result.id=issue.result at id
    rw [id]
    exact fresh
  obtain ⟨ok,synced,heads,recs,look,born,bill⟩ :=
    publish_outer_frames_exact field.result (oddAxis m) positive hQ.le birth pOK entry (externalAddrWidth tc tj (pageKeyWidth m)) ctx
      resident sync clean parsed prep out built
  let row := publishedRow entry.result birth ctx (⟨shape,out⟩ : Envelope f ell prec)
  have look' : locate issue.result pub.result.1.records=⟨some row.payload,refHeadFee key⟩ := by
    rw [←id]
    exact look
  have probeCost := build_root_probe_receipt G ell
  change B.steps=positiveTapeFee f.natDegree (Dg+1)+3 ∧ _ at probeCost
  have preCost : prep.steps≤residentsFee m q 0 (J6SourcePrecision.printed m base) r c d+(Dg+1)*(f.natDegree+2)+3*codew+12 := by
    have hfee := (probeCost.2 z).2
    change prep.steps≤residentsFee m q 0 (J6SourcePrecision.printed m base) r c d+(B.result.read z).steps+3*codew+12 at prepFee
    change (B.result.read z).steps≤(Dg+1)*(f.natDegree+2) at hfee
    omega
  refine ⟨out,N,ξ,ms,ok,synced,look',recs,bytes,trueBirth,sameCentre.trans hg.2.2.1.symm,sameCode,pageOK,
    rs,cs,roster,sem,codes,probe,?_⟩
  have portPrice : P.steps≤halfTapeFee m r c d := (generated_typed_parent_receipt G source ell atCenter).2.2
  change field.steps+B.steps+P.steps+pub.steps+4≤field.steps+
    (positiveTapeFee f.natDegree (Dg+1)+3)+halfTapeFee m r c d+
    (residentsFee m q 0 (J6SourcePrecision.printed m base) r c d+(Dg+1)*(f.natDegree+2)+3*codew+12)+
    publicationOverhead resident entry (externalAddrWidth tc tj (pageKeyWidth m))+
    framePayloadFee (J6SourcePrecision.printed m base) ell field.result.words.length (a m) 0 q codew
       (pageKeyWidth m) (M m) N (D m*K m)+shapeFrameFee prec+8
  change pub.steps=prep.steps+publicationOverhead resident entry (externalAddrWidth tc tj (pageKeyWidth m))+
    (Frames.compile prep.result field.result.hp positive hQ.le).steps+shapeFrameFee prec+4 at bill
  change (Frames.compile prep.result field.result.hp positive hQ.le).steps≤
    framePayloadFee (J6SourcePrecision.printed m base) ell field.result.words.length (a m) 0 q codew
      (pageKeyWidth m) (M m) N (D m*K m) at compFee
  rw [probeCost.1,bill]
  omega

#print axioms register_literal_odd_root
end J6R32RootGeneratedRegistryInputs
