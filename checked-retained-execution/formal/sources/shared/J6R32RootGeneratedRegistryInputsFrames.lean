
import J6R32RootGeneratedRegistryInputsProbe

/-! Exact exterior zero-mode Frames for the same stable root. This is
not the native-prefix capsule theorem with a cast. The mode and seat
compilers are independent of the exterior coordinate payload; the
probe uses its original finite word read from the positive-prefix bank. -/
namespace J6R32RootGeneratedRegistryInputs
open scoped Classical Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape
open J6R31RootResidentTables J6R30GeneratedRootLayout J6R30ProducedGateRegistry
open J6R24LegalLayout J6R14ZeroMode J6R26StablePreparedRoot J6R24MeteredRecursion
open J6R27OriginalGate J6R17ModeTape J6R15ModeCost J6R16ModeCost
open J6Mesh J6OrientedHost P11FullPacking J6R20Ancestor J6R21Ancestor J6R18ChildWrite
set_option maxHeartbeats 17500000
set_option maxRecDepth 2400

structure QueryKey (m q : ℕ) where
  seats : Word (pageKeyWidth m)
  modes : PageRef q
  group : Word 6

def QueryKey.matches {m q : ℕ} (Q : QueryKey m q)
    (page : Page (a m) (K m) (Fin 64)) (g : Fin 64) : Prop :=
  Q.seats=residentPageKey m page ∧ Q.modes=pageRef q page ∧ Q.group=word g.val

def makeOuterFrames {f : ℤ[X]} {D p q : ℕ} {W : Prescribed f D}
    (F : Frame f p) (hf : f.Monic) (probeBank : SuppliedProbeBits W f.natDegree)
    (m : ℕ) (hq : 0<q) (i : Fin (a m)) (copies prec : Word q)
    {r c d : ℕ} (source : List (SignedHalfPort r c d))
    (query : QueryKey m q) (j : Fin (D+1)) (codeWidth : ℕ) :
    Meter (Frames F.words (a m) q codeWidth (pageKeyWidth m)) :=
  let G := writeResidents m hq i copies prec source
  let Z := outerCoordinate F hf probeBank j
  ⟨⟨G.result.axis,query.modes,query.group,word 1,G.result.roster.modes,[],
      G.result.mask,query.seats,G.result.seats,Z.result⟩,
    G.steps+Z.steps+3*codeWidth+12⟩

theorem root_prescribed_frames_exact
    {V : Type} [Fintype V] {m n r c d p q ell Dg : ℕ} {T : Plant V m n}
    (source : LiteralPortFile T r c d) {f : ℤ[X]} {W : Prescribed f Dg}
    (F : Frame f p) (hf : f.Monic) (hp : 0<ell)
    (bank : SuppliedProbeBits W f.natDegree) (j : Fin (Dg+1))
    (hq : 0<q) (i : Fin (a m)) (hi : i.val+1<q)
    (copies prec : Word q) (hCopies : copies.val=K m) (hPrec : prec.val=p)
    (page : Page (a m) (K m) (Fin 64)) (g : Fin 64) (query : QueryKey m q)
    (hQ : query.matches page g)
    (codeWidth : ℕ) (codePos : 0<codeWidth)
    (refFit : 1+(writeResidents m hq i copies prec source.raw).result.roster.modes.length<2^codeWidth) :
    let R := makeOuterFrames F hf bank m hq i copies prec source.raw query j codeWidth
    let C := Frames.compile R.result F.hp hp hi.le
    let P := rootChart T
    let rs := sourceRows P i g page (actualWires m)
    let cs := sourceCols P i g page (actualWires m)
    ∃ (out : OriginFields (a m) p ell q F.words i) (N : ℕ),
      ∃ ξ : Fin N≃PacketMode i (K m) (2^(i.val+1)) p,
      ∃ ms : Fin N→ModeInput (a m) p i q,
        C.result=some out ∧
        J6R22Active.boxTransport F.exactMod (A1R10.uvRead F.hp F.words ell out.probe)=prescribedNode W p ell j ∧
        out.rows=rs.map (fun u=>slotWord P u.val) ∧
        out.cols=cs.map (fun u=>slotWord P u.val) ∧
        out.modes=List.ofFn ms ∧
        ModeMeaning P i g page (ξ.trans (packet_mode_equiv P.mask i p).symm) 0 ms ∧
        (∀ u,(ms u).code=encodeBits codeWidth u.succ.val) ∧
        R.steps≤residentsFee m q i.val p r c d+(bank.read j).steps+3*codeWidth+12 ∧
        C.steps≤framePayloadFee p ell F.words.length (a m) i.val q codeWidth
          (pageKeyWidth m) (M m) N (D m*K m) := by
  let R := makeOuterFrames F hf bank m hq i copies prec source.raw query j codeWidth
  let G := writeResidents m hq i copies prec source.raw
  let P := rootChart T
  let zeroRank : Word codeWidth := word 1
  obtain ⟨hS,hM,hG⟩ := hQ
  have oneCap : (1:ℕ)<2^codeWidth := one_lt_pow₀ (by decide) codePos.ne'
  have zVal : zeroRank.val=1 := word_val oneCap
  have cpFit : K m≤2^q := (hCopies ▸ val_lt copies).le
  have pFit : p<2^q := hPrec ▸ val_lt prec
  obtain ⟨clock,S,B,_,noDup,⟨N,ξ,raw,weights⟩,paid⟩ :=
    actual_root_resident_tables source hq i hi copies prec hCopies hPrec F.hp
  let es : Fin N→Word q := fun _=>word 0
  let β : J6R9PacketScopes.Mode i p P.mask→₀ℕ := 0
  have zeroing (u : Fin N) : (es u).val=β ((packet_mode_equiv P.mask i p).symm (ξ u)) :=
    word_val (by positivity)
  let xs := List.ofFn (fun u=>(ξ u,es u))
  have L : G.result.roster.modes.length=N := by
    rw [show G.result.roster.modes=_ from raw,List.length_ofFn]
  have fit : zeroRank.val+xs.length<2^codeWidth := by
    rw [zVal,show xs.length=N from List.length_ofFn,←L]
    exact refFit
  have rawSpec : G.result.roster.modes=xs.map (fun u=>encodeMode i u.1) := by
    simpa only [xs,List.map_ofFn] using raw
  have terms : ([] : List (RawMode q×Word q))=supportSpec G.result.roster.modes (xs.map Prod.snd) := by
    unfold xs
    rw [List.map_ofFn]
    exact (no_positive_record_for_zero G.result.roster.modes).symm
  have pages := all_root_pages m
  obtain ⟨ys,hY,sem,fee⟩ := compile_modes_exact i hi.le cpFit pFit G.result.axis clock P.mask page g
    zeroRank codePos xs fit G.result.roster.modes rawSpec noDup [] terms (orderedRootPages m) pages.2.1
    G.result.mask B
  rw [zVal] at sem
  obtain ⟨ms,eqMs,modeTrue,idCodes⟩ := meaning_of_emitted_roster P i g page ξ es β zeroing ys sem
  have Y : (compileModes i p hi.le R.result.axis R.result.owner R.result.group R.result.start
      R.result.raw R.result.sparse R.result.masks).result=some ys := by
    change (compileModes i p hi.le G.result.axis query.modes query.group zeroRank
      G.result.roster.modes [] G.result.mask).result=some ys
    rw [hM,hG]
    exact hY
  have Q : R.result.coordinates.val=List.ofFn (W.word j) := (outer_coordinate_exact F hf bank j).1
  obtain ⟨out,assembled,probe,rows,cols,modes,cost⟩ :=
    frames_with_prescribed_probe F.hp hp F.exactMod W j R.result Q hi.le ys Y
  obtain ⟨wrs,wcs⟩ := ordered_wires_exact (J6R28GeneratedRootFrame.constantRootWord m)
    (printed_room m) (printed_half_correct m)
  obtain ⟨slotMatch,slotFee,_,_,_,_⟩ := physical_slots_emitted P i (residentPageKey m)
    (resident_page_key_injective m) g page (actualWires m) wrs wcs G.result.seats S
  have hSlot : selectedSlots R.result.seatKey R.result.group R.result.seats =
      selectedSlots (residentPageKey m page) (word g.val) G.result.seats := by
    change selectedSlots query.seats query.group G.result.seats=_
    rw [hS,hG]
  rw [hSlot] at rows cols cost
  have Gfee : G.steps≤residentsFee m q i.val p r c d := paid
  have Rfee : R.steps≤residentsFee m q i.val p r c d+(bank.read j).steps+3*codeWidth+12 := by
    change G.steps+(outerCoordinate F hf bank j).steps+3*codeWidth+12≤_
    rw [(outer_coordinate_exact F hf bank j).2]
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right Gfee _) _) _
  refine ⟨out,N,ξ,ms,assembled,probe,rows.trans (congrArg Prod.fst slotMatch),
    cols.trans (congrArg Prod.snd slotMatch),modes.trans eqMs.symm,modeTrue,idCodes,Rfee,?_⟩
  let C := compileModes i p hi.le R.result.axis R.result.owner R.result.group
    R.result.start R.result.raw R.result.sparse R.result.masks
  have mfee : C.steps≤pipelineFee (a m) i.val q codeWidth N (D m*K m) := by
    change (compileModes i p hi.le G.result.axis query.modes query.group zeroRank
      G.result.roster.modes [] G.result.mask).steps≤_
    rw [hM,hG]
    simpa only [xs,List.length_ofFn,pages.2.2] using fee
  rw [actual_wires_count m] at slotFee
  change (Frames.compile R.result F.hp hp hi.le).steps≤_
  change (Frames.compile R.result F.hp hp hi.le).steps=
    F.words.length*(p+6)+A1R11.uvWidth F.words.length ell p+2+probeCopyFee p ell F.words.length+
    (selectedSlots (residentPageKey m page) (word g.val) G.result.seats).steps+C.steps+10 at cost
  rw [cost,slotFee]
  unfold framePayloadFee
  omega

#print axioms root_prescribed_frames_exact
end J6R32RootGeneratedRegistryInputs
