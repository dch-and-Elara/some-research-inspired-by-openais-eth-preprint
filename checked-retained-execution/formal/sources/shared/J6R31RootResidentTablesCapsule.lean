
import J6R31RootResidentTablesJoin
import J6R27OriginalGateCapsuleJoin

/-! For the fixed stable root and a literal legal site address, feed the
newly generated files directly to the original R27 zero-mode capsule.
There is no resident-supplied mode atlas or seat/mask table. The selected
query address and prescribed probe-coordinate word are genuine inputs;
they are not a substitute for generating its complete fine roster. -/
namespace J6R31RootResidentTables
open scoped Classical Polynomial
open Polynomial J6Mesh J6OrientedHost P11FullPacking
open AOracleMachineTime AOracleMachineTimeTape
open J6R30GeneratedRootLayout J6R24LegalLayout J6R15ModeCost J6R17ModeTape J6R27OriginalGate
open J6R18ChildWrite J6R20Ancestor J6R21Ancestor J6R22Active J6R16ModeCost
set_option maxHeartbeats 18000000
set_option maxRecDepth 2300

theorem no_positive_record_for_zero {q N : ℕ} (L : List (RawMode q)) :
    supportSpec L (List.ofFn (fun _ : Fin N=>word (q:=q) 0))=[] := by
  unfold supportSpec
  apply List.filter_eq_nil_iff.mpr
  intro b hb
  have e := (List.of_mem_zip hb).2
  obtain ⟨j,H⟩ := List.mem_ofFn.mp e
  rw [←H,word_val (show 0<(2:ℕ)^q by positivity)]
  decide

def prepareRootZero
    {q p ell : ℕ} {fw : List (A1R10.Word p)}
    (m : ℕ) (hq : 0<q) (i : Fin (a m)) (hi : i.val+1≤q)
    (copies prec : Word q) {r c d : ℕ} (input : List (SignedHalfPort r c d))
    (siteSeat : Word (pageKeyWidth m)) (siteMode : PageRef q) (group : Word 6)
    (codeWidth : ℕ) (hp : 0<p) (hℓ : 0<ell)
    (coord : {z : List Bool // z.length=fw.length}) :
    Meter (Option (OriginFields (a m) p ell q fw i)) :=
  let W := writeResidents m hq i copies prec input
  let S := selectedSlots siteSeat group W.result.seats
  let Q := compileModes i p hi W.result.axis siteMode group (word (q:=codeWidth) 1)
    W.result.roster.modes [] W.result.mask
  let Y := assembleFromProbeBits hp hℓ coord S Q
  ⟨Y.result,W.steps+Y.steps+3*codeWidth+8⟩

theorem genuine_root_zero_capsule
    {V : Type} [Fintype V] {m n r c d q p ell : ℕ}
    {T : Plant V m n} (source : LiteralPortFile T r c d)
    (hq : 0<q) (i : Fin (a m)) (hQ : i.val+1<q)
    (copies prec : Word q) (hCopies : copies.val=K m) (hPrec : prec.val=p)
    (k : Page (a m) (K m) (Fin 64)) (g : Fin 64)
    (seat : Word (pageKeyWidth m)) (seatIs : seat=residentPageKey m k)
    (mode : PageRef q) (modeIs : mode=pageRef q k)
    (gr : Word 6) (grIs : gr=word g.val)
    (codeWidth : ℕ) (codePos : 0<codeWidth)
    (codeFit : 1+(writeResidents m hq i copies prec source.raw).result.roster.modes.length<2^codeWidth)
    (hp : 0<p) (hℓ : 0<ell)
    {f : ℤ[X]} {fw : List (A1R10.Word p)}
    (hF : A1R10.Modulus p hp fw=NativeProbeRing.liftPoly p f)
    {nodeN : ℕ} (probeFit : nodeN≤2^f.natDegree) (z : Fin nodeN)
    (coord : {bs : List Bool // bs.length=fw.length})
    (hCoord : coord.val=List.ofFn (NativeProbeRing.chosenRep f.natDegree nodeN probeFit z)) :
    let O := prepareRootZero m hq i hQ.le copies prec source.raw seat mode gr codeWidth hp hℓ coord
    let L := rootChart T
    let rows := sourceRows L i g k (actualWires m)
    let cols := sourceCols L i g k (actualWires m)
    ∃ (fields : OriginFields (a m) p ell q fw i), ∃ N : ℕ,
      ∃ ξ : Fin N≃PacketMode i (K m) (2^(i.val+1)) p,
      ∃ ms : Fin N→ModeInput (a m) p i q,
      O.result=some fields ∧
      boxTransport hF (A1R10.uvRead hp fw ell fields.probe)=
        J6ActiveInterpolation.node p f ell nodeN probeFit z ∧
      fields.rows=rows.map (fun u=>slotWord L u.val) ∧
      fields.cols=cols.map (fun u=>slotWord L u.val) ∧
      fields.modes=List.ofFn ms ∧
      ModeMeaning L i g k (ξ.trans (packet_mode_equiv L.mask i p).symm) 0 ms ∧
      O.steps≤residentsFee m q i.val p r c d+
        framePayloadFee p ell fw.length (a m) i.val q codeWidth (pageKeyWidth m)
          (M m) N (D m*K m)+3*codeWidth+8 := by
  subst seat
  subst mode
  subst gr
  let W := writeResidents m hq i copies prec source.raw
  let L := rootChart T
  have Ppos : (1:ℕ)<2^codeWidth := one_lt_pow₀ (by decide) codePos.ne'
  have pFit : p<2^q := hPrec ▸ val_lt prec
  have cFit : K m≤2^q := (hCopies ▸ val_lt copies).le
  obtain ⟨hA,hS,hB,_,Rnodup,⟨N,ξ,Rcode,_⟩,paid⟩ :=
    actual_root_resident_tables source hq i hQ copies prec hCopies hPrec hp
  have len : W.result.roster.modes.length=N := by
    rw [show W.result.roster.modes=_ from Rcode,List.length_ofFn]
  have fitN : 1+N<2^codeWidth := by simpa only [←len] using codeFit
  let es : Fin N→Word q := fun _=>word 0
  let beta : J6R9PacketScopes.Mode i p L.mask→₀ℕ := 0
  have hBeta (j : Fin N) : (es j).val=beta ((packet_mode_equiv L.mask i p).symm (ξ j)) := by
    change (word (q:=q) 0).val=0
    exact word_val (by positivity)
  have ex := ordered_wires_exact (J6R28GeneratedRootFrame.constantRootWord m) (printed_room m) (printed_half_correct m)
  have pages := all_root_pages m
  obtain ⟨F,ms,exact,read,rs,cs,_,_,_,_,modes,hMeaning,ids,bill⟩ :=
    native_packet_fields_from_frames L i k g hQ.le cFit pFit W.result.axis hA
      (word (q:=codeWidth) 1) codePos (word_val Ppos) fitN ξ beta es hBeta
      W.result.roster.modes Rcode Rnodup [] (no_positive_record_for_zero W.result.roster.modes).symm
      (orderedRootPages m) pages.2.1 W.result.mask hB
      (residentPageKey m) (resident_page_key_injective m) (actualWires m) ex.1 ex.2 W.result.seats hS
      hp hℓ hF probeFit z coord hCoord
  refine ⟨F,N,ξ,ms,exact,read,rs,cs,modes,hMeaning,?_⟩
  rw [actual_wires_count m,pages.2.2] at bill
  let S := selectedSlots (residentPageKey m k) (word g.val) W.result.seats
  let Q := compileModes i p hQ.le W.result.axis (pageRef q k) (word g.val)
    (word (q:=codeWidth) 1) W.result.roster.modes [] W.result.mask
  let Y := assembleFromProbeBits hp hℓ coord S Q
  have B : Y.steps≤framePayloadFee p ell fw.length (a m) i.val q codeWidth
      (pageKeyWidth m) (M m) N (D m*K m) := bill
  change W.steps+Y.steps+3*codeWidth+8≤_
  change W.steps≤_ at paid
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add paid B) _) _

#print axioms no_positive_record_for_zero
#print axioms genuine_root_zero_capsule
end J6R31RootResidentTables
