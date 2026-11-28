import J6R33GeneratedChildSiteFrames
import J6R27OriginalGateCapsuleJoin

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 2400
set_option maxHeartbeats 13500000

/-! Each generated page is proved against the same descendant's physical
layout, in the page's own row/column selectors and actual mode meanings.
The height and common mode roster do not make pages interchangeable. -/
namespace J6R33GeneratedChildSite
open scoped Polynomial Classical
open AOracleMachineTime AOracleMachineTimeTape A1R10 J6R15ModeCost J6R17ModeTape J6R27OriginalGate
open J6R30ProducedGateRegistry J6R33PageIndexedBirth J6R32ChildResidentTransfer
open J6R10Repack P11FullPacking J6R16ModeCost J6R18ChildWrite J6R21Ancestor J6R22Active
open J6R9PacketScopes J6R9Recursive J6R20Ancestor

noncomputable def requestOfPage {a b : ℕ} (q w : ℕ) (k : Page a b (Fin 64)) :
    Request q (w+13*a) :=
  ⟨pageRef q k,childPageKey w k⟩

variable {E A B : Type} {N : Network E A B} {a q p ell code : ℕ}
  {P : PhysicalPacking N a (Fin 64)} {i : Fin a} {R : ChildResidents a q}
variable (H : ResidentReceipt P i p R) {fw : List (A1R10.Word p)}
variable {f : ℤ[X]}
variable [DecidableEq (Page a P.copies (Fin 64))]

noncomputable abbrev sitePageFee : ℕ :=
  framePayloadFee p ell fw.length a i.val (q+1) code ((q-a)+13*a) H.edges.length
    H.modes.length (orderedChildPages a P.copies).length

structure PageReceipt (C : Common fw a (q+1) code ((q-a)+13*a))
    (hp : 0<p) (hv : 0<ell) (fit : i.val+1≤q+1)
    (hMod : Modulus p hp fw=NativeProbeRing.liftPoly p f)
    (node : Box f ell p) (g : Fin 64) (β : Legal P i p) (k : Page a P.copies (Fin 64)) where
  fields : OriginFields a p ell (q+1) fw i
  modes : Fin H.modes.length→ModeInput a p i (q+1)
  hit : ((C.atRequest (requestOfPage (q+1) (q-a) k)).compile hp hv fit).result=some fields
  probe : boxTransport hMod (uvRead hp fw ell fields.probe)=node
  rowSlots : fields.rows=(sourceRows P i g k H.edges).map (fun u=>slotWord P u.val)
  colSlots : fields.cols=(sourceCols P i g k H.edges).map (fun u=>slotWord P u.val)
  rowsUnique : (sourceRows P i g k H.edges).Nodup
  colsUnique : (sourceCols P i g k H.edges).Nodup
  allRows : ∀ r,r∈sourceRows P i g k H.edges
  allCols : ∀ c,c∈sourceCols P i g k H.edges
  modeList : fields.modes=List.ofFn modes
  modeMeaning : ModeMeaning P i g k ((RosterIndex H).trans (packet_mode_equiv P.mask i p).symm) β.val modes
  modeCodes : ∀ j,(modes j).code=encodeBits code j.succ.val
  fee : ((C.atRequest (requestOfPage (q+1) (q-a) k)).compile hp hv fit).steps≤
    sitePageFee (ell:=ell) (code:=code) (fw:=fw) H

theorem rows_fit_word (g : Fin 64) (k : Page a P.copies (Fin 64)) :
    (sourceRows P i g k H.edges).length<2^(q+1) := by
  have h : (sourceRows P i g k H.edges).length≤H.edges.length :=
    List.length_filterMap_le _ _
  exact (h.trans_lt H.edgesFit).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ q))

theorem cols_fit_word (g : Fin 64) (k : Page a P.copies (Fin 64)) :
    (sourceCols P i g k H.edges).length<2^(q+1) := by
  have h : (sourceCols P i g k H.edges).length≤H.edges.length :=
    List.length_filterMap_le _ _
  exact (h.trans_lt H.edgesFit).trans_le (Nat.pow_le_pow_right (by decide) (Nat.le_succ q))

theorem fixed_page_compiles {tw bw n : ℕ} (X : ActiveWords fw (q+1) tw bw)
    (clock : X.axis.length=i.val) (g : Fin 64) (hG : X.group.val=g.val)
    (codePos : 0<code) (codeFit : 1+H.modes.length<2^code)
    (β : Legal P i p)
    (hβ : X.exponents.map Word.val=H.modes.map (fun m=>β.val ((packet_mode_equiv P.mask i p).symm m)))
    (hp : 0<p) (hv : 0<ell) (qFit : i.val+1≤q+1)
    (hMod : Modulus p hp fw=NativeProbeRing.liftPoly p f)
    (probeFit : n≤2^f.natDegree) (z : Fin n)
    (hZ : X.coordinates.val=List.ofFn (NativeProbeRing.chosenRep f.natDegree n probeFit z))
    (k : Page a P.copies (Fin 64)) :
    Nonempty (PageReceipt H (commonView code R X) hp hv qFit hMod
      (J6ActiveInterpolation.node p f ell n probeFit z) g β k) := by
  let rk : J6R15ModeCost.Word code := word 1
  have rank1 : rk.val=1 := word_val (one_lt_pow₀ (by decide) codePos.ne')
  have pp : p<2^(q+1) := H.prec ▸ val_lt R.raw.roster.precision
  have cp : P.copies≤2^(q+1) := (H.copyValue ▸ val_lt R.raw.copies).le
  have gWord : X.group=word g.val :=
    (valued_word X.group).symm.trans (congrArg word hG)
  obtain ⟨es,eS,eV⟩ := fixed_event_exponents H β X.exponents hβ
  have spec : supportSpec R.raw.roster.modes X.exponents=
      supportSpec R.raw.roster.modes (List.ofFn es) := congrArg _ eS
  let keys := orderedChildPages a P.copies
  obtain ⟨fld,ms,hit,probe,rs,cs,unR,unC,allR,allC,modeSpec,modeTrue,codes,paid⟩ :=
    native_packet_fields_from_frames P i k g qFit cp pp X.axis clock rk codePos rank1 codeFit
      (RosterIndex H) β.val es eV R.raw.roster.modes (roster_index_mapped H) H.rawUnique
      (supportSpec R.raw.roster.modes X.exponents) spec keys (child_pages_complete _ _).2.1
      R.raw.masks H.masks (childPageKey (q-a)) (child_page_key_injective (q-a) H.copiesFit)
      H.edges H.edgesUnique H.edgesAll R.seats H.seats hp hv hMod probeFit z X.coordinates hZ
  let C := commonView code R X
  have frame : ((C.atRequest (requestOfPage (q+1) (q-a) k)).compile hp hv qFit)=
      assembleFromProbeBits hp hv X.coordinates
        (selectedSlots (childPageKey (q-a) k) (word g.val) R.seats)
        (compileModes i p qFit X.axis (pageRef (q+1) k) (word g.val) rk R.raw.roster.modes
          (supportSpec R.raw.roster.modes X.exponents) R.raw.masks) := by
    unfold C commonView Common.atRequest Frames.compile requestOfPage
    dsimp only
    rw [gWord]
  refine ⟨⟨fld,ms,?_,probe,rs,cs,unR,unC,allR,allC,modeSpec,modeTrue,codes,?_⟩⟩
  · rw [frame]
    exact hit
  · rw [frame]
    exact paid

#print axioms rows_fit_word
#print axioms cols_fit_word
#print axioms fixed_page_compiles
end J6R33GeneratedChildSite
