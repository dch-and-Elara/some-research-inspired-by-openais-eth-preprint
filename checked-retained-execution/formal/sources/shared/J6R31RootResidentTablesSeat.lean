
import J6R31RootResidentTablesGeometry
import J6R27OriginalGateCapsuleJoin

/-! Produce the fixed R27 SeatField ABI from the actual R30 rooted
port file. Copying an address or a group word is not a free scalar
operation. This is the stable initial chart only, not cast to any
descendant's changing masks. -/
namespace J6R31RootResidentTables
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape J6R12CollisionEdges
open J6R30GeneratedRootLayout J6R24LegalLayout J6R14LayoutCost J6R23PaddingCensus
open J6Mesh J6OrientedHost P11FullPacking J6R15ModeCost J6R27OriginalGate
open J6R20Ancestor
set_option maxHeartbeats 13000000
set_option maxRecDepth 2000

def fitBits : ℕ→List Bool→Meter (List Bool)
  | 0,_ => ⟨[],2⟩
  | n+1,x =>
    let p := fitBits n x.tail
    ⟨x.headD false::p.result,p.steps+6⟩

theorem fit_bits_shape (n : ℕ) (xs : List Bool) :
    (fitBits n xs).result.length=n ∧ (fitBits n xs).steps=2+6*n := by
  induction n generalizing xs with
  | zero => simp [fitBits]
  | succ n ih =>
    obtain ⟨h,r⟩ := ih xs.tail
    simp only [fitBits,List.length_cons,h,r,Nat.mul_succ]
    exact ⟨True.intro,by omega⟩

def fitWord (n : ℕ) (xs : List Bool) : Meter (Word n) :=
  let z := fitBits n xs
  ⟨⟨z.result,(fit_bits_shape n xs).1⟩,z.steps⟩

theorem fit_word_value (n : ℕ) (xs : List Bool) (len : xs.length=n) :
    (fitWord n xs).result.bits=xs := by
  change (fitBits n xs).result=xs
  induction xs generalizing n with
  | nil => subst n; rfl
  | cons x xs ih =>
    subst n
    change x::(fitBits xs.length xs).result=x::xs
    rw [ih _ rfl]

theorem fit_word_fee (n : ℕ) (xs : List Bool) : (fitWord n xs).steps=2+6*n :=
  (fit_bits_shape n xs).2

def emitAxisTape : List AxisWord→List Bool→Meter (List Bool)
  | x::xs,b::bs =>
    let z := emitAxisTape xs bs
    let h := appendBits x.high ((x.unequal && b)::z.result)
    let l := appendBits x.low h.result
    ⟨l.result,l.steps+h.steps+z.steps+8⟩
  | _,_=>⟨[],3⟩

theorem emit_axis_tape_exact (xs : List AxisWord) (bs : List Bool)
    (fit : ∀ x∈xs,x.low.length=6 ∧ x.high.length=6) :
    (emitAxisTape xs bs).result=axisPayload xs bs ∧
      (emitAxisTape xs bs).steps≤3+60*xs.length := by
  induction xs generalizing bs with
  | nil => simp [emitAxisTape,axisPayload]
  | cons x xs ih =>
    cases bs with
    | nil => simp [emitAxisTape,axisPayload]
    | cons b bs =>
      obtain ⟨lo,hi⟩ := fit x List.mem_cons_self
      obtain ⟨e,n⟩ := ih bs (fun x hx=>fit x (List.mem_cons_of_mem _ hx))
      constructor
      · simp only [emitAxisTape,append_bits_exact,axisPayload,List.zip_cons_cons,List.flatMap_cons,
          axisBytes,List.append_assoc,List.singleton_append]
        rw [e]
        rfl
      · simp only [emitAxisTape,append_bits_exact,lo,hi,List.length_cons,Nat.mul_succ]
        omega

def pageKeyWidth (m : ℕ) := RootKey m+13*a m

def residentPageKey (m : ℕ) (page : Page (a m) (K m) (Fin 64)) : Word (pageKeyWidth m) :=
  ⟨(pageWord (RootKey m) page).val,(pageWord (RootKey m) page).property⟩

theorem resident_page_key_injective (m : ℕ) : Function.Injective (residentPageKey m) := by
  intro p q eq
  apply (page_code_injective (RootKey m) ?_).eq_iff.mp
  · exact congrArg (fun w : Word (pageKeyWidth m)=>w.val) eq
  · have L := (printed_rank_width m).2.2
    have h := (printed_rank_width m).2.1
    have D : K m*2^(a m)<2^RootKey m*2^(a m) := by
      rw [←pow_add,RootKey,Nat.sub_add_cancel h]
      exact L
    exact (Nat.lt_of_mul_lt_mul_right D).le

def seatStride (a w : ℕ) := 200*a+10*w+200

def buildSeatField (a w : ℕ) (axis : List Bool) (x : AnchorWord) :
    Meter (SeatField a (w+13*a)) :=
  let S := emitAxisTape x.physical.axes x.physical.seat.selector
  let join := appendBits x.physical.seat.page S.result
  let pg := fitWord (w+13*a) join.result
  let sl := fitWord a x.physical.seat.slot
  let R := readSymbol axis x.cell.1
  let C := readSymbol axis x.cell.2
  let row := fitWord 6 R.result
  let col := fitWord 6 C.result
  ⟨⟨pg.result,sl.result,row.result,col.result⟩,
    S.steps+join.steps+pg.steps+sl.steps+R.steps+C.steps+row.steps+col.steps+12⟩

noncomputable abbrev rootChart {V : Type} [Fintype V] {m n : ℕ} (T : Plant V m n) :=
  stableRootPacking m (printedHalf m) n (printedRankWidth m) T
    (J6R28GeneratedRootFrame.constantRootWord m) (printed_room m) (printed_half_correct m)
    (printed_rank_width m).2.1 (printed_rank_width m).2.2.le

theorem source_seat_field {V : Type} [Fintype V] {m n r c d : ℕ} {T : Plant V m n}
    (P : LiteralPortFile T r c d) (i : Fin (a m)) (axis : List Bool) (clock : axis.length=i.val)
    (e : RootWire m) :
    let x := (sourceAnchor m e).anchor
    let O := buildSeatField (a m) (RootKey m) axis x
    O.result=physicalSeatField (rootChart T) i (residentPageKey m) e ∧
      O.steps≤seatStride (a m) (RootKey m) := by
  let x := (sourceAnchor m e).anchor
  let s := x.physical.seat
  let layout := rootChart T
  let u := (rankAt m e).1
  obtain ⟨hAx,hPage,hSlot,hSel⟩ := words_shape m e
  obtain ⟨hFit,correct⟩ := serialized_same_stable_seat P e
  change decodePhysical u s hFit=layout.seat e at correct
  have cell := serialized_cell_same_stable P e
  change x.cell=wordCell (physicalCell (fun _ _ _=>false) (layout.seat e)) at cell
  have O := emit_axis_tape_exact x.physical.axes s.selector (fun y hy=>by
    rw [hAx,axesOf,List.mem_ofFn] at hy
    obtain ⟨j,rfl⟩ := hy
    exact ⟨symbol_length _,symbol_length _⟩)
  have E : (appendBits s.page (emitAxisTape x.physical.axes s.selector).result).result=
      (residentPageKey m (layout.seat e).1).bits := by
    rw [append_bits_exact,O.1]
    change s.page++axisPayload x.physical.axes s.selector=_
    rw [hAx,←correct]
    exact decode_page_fields u s hSel hPage hFit
  have K : s.slot=(slotWord layout e).bits := by
    change s.slot=encodeBits (a m) (layout.seat e).2.val
    rw [←correct]
    exact decode_slot_literal u s hSlot hFit
  let v := physicalCell (fun _ _ _=>false) (layout.seat e)
  have vl : (readSymbol axis x.cell.1).result=symbol ((v i).1) := by
    rw [cell]
    exact coordinate_word_at i axis clock (fun j=>(v j).1)
  have vr : (readSymbol axis x.cell.2).result=symbol ((v i).2) := by
    rw [cell]
    exact coordinate_word_at i axis clock (fun j=>(v j).2)
  constructor
  · change SeatField.mk _ _ _ _=physicalSeatField layout i (residentPageKey m) e
    unfold physicalSeatField
    congr 1
    · apply word_bits_inj
      rw [fit_word_value]
      · exact E
      · rw [E]
        exact (residentPageKey m (layout.seat e).1).size
    · apply word_bits_inj
      rw [fit_word_value _ _ hSlot]
      exact K
    · apply word_bits_inj
      rw [vl,fit_word_value _ _ (symbol_length _)]
      rfl
    · apply word_bits_inj
      rw [vr,fit_word_value _ _ (symbol_length _)]
      rfl
  · have A : (emitAxisTape x.physical.axes s.selector).steps≤3+60*a m := by
      calc
        _≤3+60*x.physical.axes.length := O.2
        _=_ := by rw [hAx,axesOf,List.length_ofFn]
    have Pg : s.page.length=RootKey m := hPage
    have b := read_symbol_fee axis x.cell.1
    have d := read_symbol_fee axis x.cell.2
    have ai : axis.length≤a m := clock ▸ i.isLt.le
    let S := emitAxisTape x.physical.axes s.selector
    let J := appendBits s.page S.result
    let l := readSymbol axis x.cell.1
    let r := readSymbol axis x.cell.2
    change S.steps+J.steps+(fitWord (RootKey m+13*a m) J.result).steps+
      (fitWord (a m) s.slot).steps+l.steps+r.steps+
      (fitWord 6 l.result).steps+(fitWord 6 r.result).steps+12≤_
    have hJ : J.steps=2+4*RootKey m := by unfold J; rw [append_bits_exact]; exact congrArg (fun n=>2+4*n) Pg
    change S.steps≤_ at A
    change l.steps≤_ at b
    change r.steps≤_ at d
    rw [hJ]
    simp only [fit_word_fee]
    unfold seatStride
    omega

def rootSeats {r c d : ℕ} (m : ℕ) (axis : List Bool)
    (raw : List (SignedHalfPort r c d)) : Meter (List (SeatField (a m) (pageKeyWidth m))) :=
  let T := generatedPaddedPorts m raw
  let O := mapMeter (fun row=>buildSeatField (a m) (RootKey m) axis row.base.anchor.anchor) T.result
  ⟨O.result,T.steps+O.steps+4⟩

def seatsFee (m r c d : ℕ) :=
  paddedPortsFee m r c d+M m*(seatStride (a m) (RootKey m)+6)+4

theorem root_seat_table_exact {V : Type} [Fintype V] {m n r c d : ℕ} {T : Plant V m n}
    (P : LiteralPortFile T r c d) (i : Fin (a m)) (axis : List Bool) (clock : axis.length=i.val) :
    let Z := rootSeats m axis P.raw
    Z.result=(actualWires m).map (physicalSeatField (rootChart T) i (residentPageKey m)) ∧
      Z.steps≤seatsFee m r c d := by
  obtain ⟨eq,len,_,cost⟩ := generated_padded_ports_exact P
  let field := physicalSeatField (rootChart T) i (residentPageKey m)
  let f (row : MountedPort r c d) := buildSeatField (a m) (RootKey m) axis row.base.anchor.anchor
  let raw := (generatedPaddedPorts m P.raw).result
  let Z := mapMeter f raw
  have h (row : MountedPort r c d) (hrow : row∈raw) :
      (f row).result=(f row).result ∧ (f row).steps≤seatStride (a m) (RootKey m) := by
    change row∈(generatedPaddedPorts m P.raw).result at hrow
    rw [eq,List.mem_map] at hrow
    obtain ⟨e,_,rfl⟩ := hrow
    exact ⟨rfl,(source_seat_field P i axis clock e).2⟩
  obtain ⟨form,fee⟩ := mapMeter_exact f (fun row=>(f row).result) _ raw h
  change Z.result=_ at form
  change Z.steps≤(seatStride (a m) (RootKey m)+6)*raw.length at fee
  change Z.result=_ ∧ (generatedPaddedPorts m P.raw).steps+Z.steps+4≤_
  constructor
  · change raw=(actualWires m).map (trueMounted P) at eq
    rw [form,eq,List.map_map]
    apply List.map_congr_left
    intro e _
    exact (source_seat_field P i axis clock e).1
  · change raw.length=M m at len
    rw [len,Nat.mul_comm _ (M m)] at fee
    unfold seatsFee
    omega

#print axioms fit_word_value
#print axioms emit_axis_tape_exact
#print axioms resident_page_key_injective
#print axioms source_seat_field
#print axioms root_seat_table_exact
end J6R31RootResidentTables
