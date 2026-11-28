
import J6R24LegalLayoutTable
import J6R23PaddingCensusCodec

/-! Convert the existing paid R14/R24 header words directly to the
R23 census address format. The dependent physical decode is used
only in the correctness statement, never in this bit program. -/
namespace J6R25StableCensus
open scoped Classical BigOperators
open P11FullPacking A1R10 A1R12 AOracleMachineTime AOracleMachineTimeTape
open J6R24LegalLayout J6R23PaddingCensus J6R14LayoutCost J6R12CollisionMenu
set_option maxHeartbeats 18500000
set_option linter.unusedSectionVars false

def fuseAxes : List AxisWord→List Bool→Meter (List Bool)
  | x::xs,b::bs =>
    let f := fuseAxes xs bs
    ⟨x.low++(x.high++(b::f.result)),f.steps+64⟩
  | _,_ => ⟨[],4⟩

def seatCodecFee (a q : ℕ) := 4+64*a+12*(q+15*a+3)

def encodeRawSeat (a q : ℕ) (r : RawAddress) : Meter (SeatWord (q-a+13*a) (a+1)) :=
  let p := fuseAxes r.axes r.seat.selector
  let head := asLowWord (q-a+13*a) (r.seat.page++p.result)
  let tail := asLowWord (a+1) r.seat.slot
  ⟨⟨head,tail⟩,p.steps+12*(q+15*a+3)⟩

private theorem ofFn_lookup (n : ℕ) (l : List Bool) (h : l.length=n) :
    List.ofFn (fun i : Fin n=>l.getD i.val false)=l := by
  apply List.ext_getElem (by simp [h])
  intro i h₁ h₂
  rw [List.getElem_ofFn]
  simp [List.getD_eq_getElem?_getD,h₂]

private theorem align_fuse {n : ℕ} (xs : Fin n→AxisWord) (flags : Fin n→Bool)
    (ys : Fin n→Word 13)
    (eq : ∀ i,(ys i).val=(xs i).low++((xs i).high++[flags i])) :
    (fuseAxes (List.ofFn xs) (List.ofFn flags)).result=fixedConcat (List.ofFn ys) ∧
      (fuseAxes (List.ofFn xs) (List.ofFn flags)).steps=4+64*n := by
  induction n with
  | zero => simp [fuseAxes,fixedConcat]
  | succ n ih =>
    have h := ih (fun j=>xs j.succ) (fun j=>flags j.succ) (fun j=>ys j.succ) (fun j=>eq j.succ)
    constructor
    · simp only [List.ofFn_succ,fuseAxes,fixedConcat,h.1,eq,List.append_assoc,List.singleton_append]
    · simp only [List.ofFn_succ,fuseAxes,h.2]
      omega

private theorem codec_slot_value (a : ℕ) (slot : List Bool) (h : slot.length=a) :
    let r := (bitsChart a).symm (fun i=>slot.getD i.val false)
    r.val=bitsValue slot := by
  let r : Fin (2^a) := ⟨bitsValue slot,by simpa only [h] using bitsValue_lt slot⟩
  have e : slot=encodeBits a (bitsValue slot) :=
    equal_width_inj (by rw [encodeBits_length,h]) (encodeBits_exact _ _ r.isLt).symm
  have V : (fun i : Fin a=>slot.getD i.val false)=bits a r := by
    funext i
    rw [e]
    exact encode_getD a (bitsValue slot) i.val i.isLt
  dsimp only
  rw [V]
  exact congrArg Fin.val ((bitsChart a).symm_apply_apply r)

theorem anchor_census_format {a b q : ℕ} (ha : a≤q) (cap : b*2^a≤2^q) (x : FullRank a b) :
    let out := encodeRawSeat a q (anchorAt q x).physical
    out.result.represents (pageCode (q-a)) (fullStable ha cap x) ∧
      out.steps=seatCodecFee a q := by
  let rank := encodeBits q x.2.val
  let H := exportOne a (wordCell x.1) rank
  let raw := H.result
  let S := seatWords (marksOf x.1) rank
  have mr : (marksOf x.1).length≤rank.length := by rw [marksOf_len,encodeBits_length]; exact ha
  have hbit : bitsValue rank<b*2^a := by
    change bitsValue (encodeBits q x.2.val)<_
    rw [encodeBits_exact _ _ (x.2.isLt.trans_le cap)]
    exact x.2.isLt
  obtain ⟨pH,axes,_,_,_,_⟩ := exportOne_exact x.1 rank (by simpa only [rank,encodeBits_length]) hbit
  have seat : raw.seat=S.result := by
    change (seatWords (prepareHeader a (wordCell x.1)).result.2 rank).result=_
    rw [(prepareHeader_exact x.1).1]
  obtain ⟨_p,W⟩ := anchor_decodes ha cap x
  let z := decodePhysical x.1 raw.seat pH
  have toZ : z=fullStable ha cap x := W
  have axisEq : raw.axes=axesOf x.1 := axes
  obtain ⟨lenS,lenF,_,_,lenP,_⟩ := seatWords_exact (marksOf x.1) rank mr
  rw [marksOf_len] at lenS lenF lenP
  have fLen : raw.seat.selector.length=a := by rw [seat]; exact lenF
  have sLen : raw.seat.slot.length=a := by rw [seat]; exact lenS
  have pLen : raw.seat.page.length=q-a := by rw [seat,lenP,List.length_drop,encodeBits_length]
  let flags := fun i : Fin a=>raw.seat.selector.getD i.val false
  have flagged (i : Fin a) : axisSelector z.1 i=flags i := by
    by_cases hot : ((key x.1).val i).1≠((key x.1).val i).2
    · change (if u : ((key x.1).val i).1≠((key x.1).val i).2 then
        raw.seat.selector.getD i.val false else false)=_
      rw [dif_pos hot]
    · have hh : (x.1 i).1=(x.1 i).2 := not_ne_iff.mp (fun H=>hot ((hot_iff x.1 i).2 H))
      have ff : raw.seat.selector.getD i.val false=false := by rw [seat]; exact selectorAt_equal x.1 rank i hh
      change axisSelector (decodePhysical x.1 raw.seat pH).1 i=_
      unfold axisSelector
      change (if h : ((key x.1).val i).1≠((key x.1).val i).2 then
        raw.seat.selector.getD i.val false else false)=_
      rw [dif_neg hot]
      exact ff.symm
  have eAxes (i : Fin a) :
      (axisRecord z.1 i).val=(axisSpec (x.1 i).1 (x.1 i).2).low++
        ((axisSpec (x.1 i).1 (x.1 i).2).high++[flags i]) := by
    have e := flagged i
    unfold axisRecord axisSpec
    rw [e]
    rfl
  have glue := align_fuse (fun i=>axisSpec (x.1 i).1 (x.1 i).2) flags (axisRecord z.1) eAxes
  have realFuse : (fuseAxes raw.axes raw.seat.selector).result=fixedConcat (List.ofFn (axisRecord z.1)) ∧
      (fuseAxes raw.axes raw.seat.selector).steps=4+64*a := by
    unfold axesOf at axisEq
    rw [axisEq,←ofFn_lookup a raw.seat.selector fLen]
    exact glue
  have pageEncoding : raw.seat.page=encodeBits (q-a) z.1.2.1.val := by
    apply equal_width_inj (by rw [pLen,encodeBits_length])
    have b := bitsValue_lt raw.seat.page
    rw [pLen] at b
    change bitsValue raw.seat.page=bitsValue (encodeBits (q-a) (bitsValue raw.seat.page))
    rw [encodeBits_exact _ _ b]
  have fullPage : raw.seat.page++(fuseAxes raw.axes raw.seat.selector).result=(pageWord (q-a) z.1).val := by
    unfold pageWord
    rw [pageEncoding,realFuse.1]
  have sg : bitsValue raw.seat.slot=z.2.val := (codec_slot_value a raw.seat.slot sLen).symm
  have near : bitsValue raw.seat.slot<2^(a+1) := by
    have b := bitsValue_lt raw.seat.slot
    rw [sLen] at b
    exact b.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  dsimp only
  rw [←toZ]
  refine ⟨⟨?_,?_⟩,?_⟩
  · change bitsValue (lowBits (q-a+13*a) (raw.seat.page++(fuseAxes raw.axes raw.seat.selector).result)) = pageCode (q-a) z.1
    rw [lowBits_value,fullPage,Nat.mod_eq_of_lt (by
      have hb := bitsValue_lt (pageWord (q-a) z.1).val
      rwa [(pageWord (q-a) z.1).property] at hb)]
    rfl
  · change bitsValue (lowBits (a+1) raw.seat.slot)=z.2.val
    rw [lowBits_value,Nat.mod_eq_of_lt near,sg]
  · change (fuseAxes raw.axes raw.seat.selector).steps+12*(q+15*a+3)=_
    rw [realFuse.2]
    rfl

#print axioms anchor_census_format
end J6R25StableCensus
