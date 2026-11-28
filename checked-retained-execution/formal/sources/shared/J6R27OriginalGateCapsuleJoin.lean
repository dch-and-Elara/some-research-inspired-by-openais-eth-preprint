
import J6R27OriginalGateProbeCapsule
import J6R27OriginalGateModePipeline
import J6R27OriginalGateSlots

/-! One real generated packet's complete typed OriginFields payload
from the resident physical ABI. The output is ready for the R21
native entry reader. Registry insertion and production of each preceding
resident source file remain separate steps. -/
namespace J6R27OriginalGate
open scoped Polynomial
open AOracleMachineTime AOracleMachineTimeTape A1R10 A1R11
open J6R17ModeTape J6R16ModeCost J6R21Ancestor J6R18ChildWrite J6R22Active
open P11FullPacking J6R10Repack J6R20Ancestor

def framePayloadFee (p ell deg a i q codew pagew edges modes pages : ℕ) :=
  deg*(p+6)+uvWidth deg ell p+2+probeCopyFee p ell deg+
  (4+edges*slotStride a pagew)+pipelineFee a i q codew modes pages+10

variable {E A B : Type} {N : Network E A B}
variable {a p ell q codew pagew modeN nodeN : ℕ}
variable {f : ℤ[X]}

set_option maxHeartbeats 4700000 in
theorem native_packet_fields_from_frames (P : PhysicalPacking N a (Fin 64))
    (i : Fin a) (k : Page a P.copies (Fin 64)) (g : Fin 64)
    [DecidableEq (Page a P.copies (Fin 64))]
    (qFit : i.val+1≤q) (pageFit : P.copies≤2^q) (pFit : p<2^q)
    (axis : List Bool) (clock : axis.length=i.val)
    (rank : J6R15ModeCost.Word codew) (bPos : 0<codew) (first : rank.val=1)
    (codeFit : 1+modeN<2^codew)
    (ξ : Fin modeN≃PacketMode i P.copies (2^(i.val+1)) p)
    (β : J6R9PacketScopes.Mode i p P.mask→₀ℕ) (es : Fin modeN→J6R15ModeCost.Word q)
    (tuple : ∀ j,(es j).val=β ((packet_mode_equiv P.mask i p).symm (ξ j)))
    (raw : List (RawMode q)) (roster : raw=List.ofFn (fun j=>encodeMode i (ξ j))) (rawN : raw.Nodup)
    (sparse : List (RawMode q×J6R15ModeCost.Word q))
    (terms : sparse=supportSpec raw (List.ofFn es))
    (pages : List (Page a P.copies (Fin 64))) (allPages : ∀ page,page∈pages)
    (bank : List (MaskRow q)) (maskWord : bank=pages.map (encodeMaskRow P.mask))
    (key : Page a P.copies (Fin 64)→J6R15ModeCost.Word pagew) (hKey : Function.Injective key)
    (edges : List E) (nodup : edges.Nodup) (allEdges : ∀ e,e∈edges)
    (seats : List (SeatField a pagew)) (seatWord : seats=edges.map (physicalSeatField P i key))
    (hp : 0<p) (hv : 0<ell) {fw : List (A1R10.Word p)}
    (hMod : Modulus p hp fw=NativeProbeRing.liftPoly p f)
    (probeFit : nodeN≤2^f.natDegree) (z : Fin nodeN)
    (coord : {bits : List Bool // bits.length=fw.length})
    (hCoord : coord.val=List.ofFn (NativeProbeRing.chosenRep f.natDegree nodeN probeFit z)) :
    let S := selectedSlots (key k) (J6R15ModeCost.word g.val) seats
    let M := compileModes i p qFit axis (pageRef q k) (J6R15ModeCost.word g.val) rank raw sparse bank
    let T := assembleFromProbeBits hp hv coord S M
    let R := sourceRows P i g k edges
    let C := sourceCols P i g k edges
    ∃ (F : OriginFields a p ell q fw i) (ms : Fin modeN→ModeInput a p i q),
      T.result=some F ∧
      boxTransport hMod (uvRead hp fw ell F.probe)=J6ActiveInterpolation.node p f ell nodeN probeFit z ∧
      F.rows=R.map (fun r=>slotWord P r.val) ∧ F.cols=C.map (fun c=>slotWord P c.val) ∧
      R.Nodup ∧ C.Nodup ∧ (∀ r,r∈R) ∧ (∀ c,c∈C) ∧
      F.modes=List.ofFn ms ∧
      ModeMeaning P i g k (ξ.trans (packet_mode_equiv P.mask i p).symm) β ms ∧
      (∀ j,(ms j).code=encodeBits codew j.succ.val) ∧
      T.steps≤framePayloadFee p ell fw.length a i.val q codew pagew edges.length modeN pages.length := by
  let X := List.ofFn (fun j=>(ξ j,es j))
  have h1 : raw=X.map (fun x=>encodeMode (q:=q) i x.1) := by
    simpa only [X,List.map_ofFn] using roster
  have h2 : sparse=supportSpec raw (X.map Prod.snd) := by
    simpa only [X,List.map_ofFn] using terms
  have hWidth : rank.val+X.length<2^codew := by
    change rank.val+(List.ofFn _).length<_
    rw [List.length_ofFn,first]
    exact codeFit
  obtain ⟨ys,mRead,mSpec,mFee⟩ := compile_modes_exact i qFit pageFit pFit axis clock P.mask k g
    rank bPos X hWidth raw h1 rawN sparse h2 pages allPages bank maskWord
  rw [first] at mSpec
  obtain ⟨ms,listWord,modeTrue,codes⟩ := meaning_of_emitted_roster P i g k ξ es β tuple ys mSpec
  obtain ⟨slotValue,slotFee,rN,cN,rAll,cAll⟩ :=
    physical_slots_emitted P i key hKey g k edges nodup allEdges seats seatWord
  let S := selectedSlots (key k) (J6R15ModeCost.word g.val) seats
  let M := compileModes i p qFit axis (pageRef q k) (J6R15ModeCost.word g.val) rank raw sparse bank
  obtain ⟨F,hRead,hProbe,rs,cs,fieldM,bill⟩ :=
    actual_probe_capsule hp hv hMod probeFit z coord hCoord S M ys mRead
  refine ⟨F,ms,hRead,hProbe,rs.trans (congrArg Prod.fst slotValue),
    cs.trans (congrArg Prod.snd slotValue),rN,cN,rAll,cAll,
    fieldM.trans listWord.symm,modeTrue,codes,?_⟩
  change M.steps≤pipelineFee a i.val q codew X.length pages.length at mFee
  have hL : X.length=modeN := List.length_ofFn
  rw [hL] at mFee
  rw [bill,slotFee]
  unfold framePayloadFee
  omega

#print axioms native_packet_fields_from_frames
end J6R27OriginalGate


