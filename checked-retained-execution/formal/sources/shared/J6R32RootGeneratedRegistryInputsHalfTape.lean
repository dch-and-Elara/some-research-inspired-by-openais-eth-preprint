
import J6R31RootResidentTablesSeat
import J6R25PreparedSupplyPhysicalPorts

/-! A finite physical half-port header tape from the same stable
root seats. Every occupied seat writes two independent sides, their
actual group and the full page/slot payload. No address order from a
future layout is used. This descriptor does not itself evaluate Gates. -/
namespace J6R32RootGeneratedRegistryInputs
open scoped Classical
open AOracleMachineTime J6R30GeneratedRootLayout J6R31RootResidentTables
open J6R27OriginalGate J6R15ModeCost J6R25PreparedSupply
open J6R17ModeTape J6R10Repack J6Mesh J6OrientedHost
set_option maxHeartbeats 12000000
set_option maxRecDepth 2150

def rootHalfWidth (m : ℕ) := 1+(pageKeyWidth m+a m)

def halfPortSpec (m : ℕ) (b : Bool) (field : SeatField (a m) (pageKeyWidth m)) :
    PortRow (rootHalfWidth m) :=
  let tape := field.page.bits++field.slot.bits
  let addr : Word (rootHalfWidth m) := ⟨b::tape,by
    unfold rootHalfWidth
    change (b::field.page.bits++field.slot.bits).length=_
    simp only [List.length_cons,List.length_append,field.page.size,field.slot.size]
    omega⟩
  ⟨addr,(if b then field.colGroup else field.rowGroup),tape⟩

def encodeHalfPair (m : ℕ) (field : SeatField (a m) (pageKeyWidth m)) :
    Meter (List (PortRow (rootHalfWidth m))) :=
  let raw := appendBits field.page.bits field.slot.bits
  let l := copyFixed field.rowGroup
  let r := copyFixed field.colGroup
  let kw : raw.result.length=pageKeyWidth m+a m := by
    change (appendBits field.page.bits field.slot.bits).result.length=_
    rw [append_bits_exact,List.length_append,field.page.size,field.slot.size]
  ⟨[⟨⟨false::raw.result,by unfold rootHalfWidth; simp only [List.length_cons,kw]; omega⟩,l.result,raw.result⟩,
    ⟨⟨true::raw.result,by unfold rootHalfWidth; simp only [List.length_cons,kw]; omega⟩,r.result,raw.result⟩],
    raw.steps+l.steps+r.steps+2*(rootHalfWidth m+pageKeyWidth m+a m+12)⟩

def halfPairFee (m : ℕ) := 4*pageKeyWidth m+40+2*(rootHalfWidth m+pageKeyWidth m+a m+12)

theorem half_pair_exact (m : ℕ) (F : SeatField (a m) (pageKeyWidth m)) :
    encodeHalfPair m F=⟨[halfPortSpec m false F,halfPortSpec m true F],halfPairFee m⟩ := by
  unfold encodeHalfPair halfPortSpec halfPairFee
  simp only [append_bits_exact,copy_fixed_exact,F.page.size,Bool.false_eq_true,if_false,if_true]
  congr 1
  omega

def sided {E : Type*} (x : E×Bool) : Port E := if x.2 then .inr x.1 else .inl x.1

theorem sided_injective {E : Type*} : Function.Injective (sided (E:=E)) := by
  rintro ⟨x,a⟩ ⟨y,b⟩ h
  cases a <;> cases b <;> simp_all [sided]

noncomputable def rootHalfOrder (m : ℕ) :=
  ((actualWires m) ×ˢ ([false,true] : List Bool)).map sided

theorem root_half_order_complete (m : ℕ) :
    (rootHalfOrder m).Nodup ∧ (∀ e,e∈rootHalfOrder m) ∧ (rootHalfOrder m).length=2*M m := by
  have S : ([false,true] : List Bool).Nodup := by decide
  have W := J6R24LegalLayout.ordered_wires_exact
    (J6R28GeneratedRootFrame.constantRootWord m) (J6R24LegalLayout.printed_room m)
      (J6R24LegalLayout.printed_half_correct m)
  have f (b : Bool) : b∈([false,true] : List Bool) := by cases b <;> decide
  unfold rootHalfOrder
  refine ⟨(W.1.product S).map sided_injective,?_,?_⟩
  · rintro (x|x)
    · exact List.mem_map.mpr ⟨(x,false),List.mem_product.mpr ⟨W.2 x,f false⟩,rfl⟩
    · exact List.mem_map.mpr ⟨(x,true),List.mem_product.mpr ⟨W.2 x,f true⟩,rfl⟩
  · rw [List.length_map,List.length_product,actual_wires_count]
    simp only [List.length_cons,List.length_nil,Nat.zero_add]
    omega

noncomputable def expectedHalfRow {V : Type} [Fintype V] {m n : ℕ} (T : Plant V m n)
    (i : Fin (a m)) (x : Port (RootWire m)) :=
  halfPortSpec m (side x) (physicalSeatField (rootChart T) i (residentPageKey m) (edge x))

theorem half_addresses_unique {V : Type} [Fintype V] {m n : ℕ} (T : Plant V m n)
    (i : Fin (a m)) : Function.Injective (fun x=>(expectedHalfRow T i x).address) := by
  let P := rootChart T
  intro x y he
  have eq0 := congrArg Word.bits he
  change side x::((residentPageKey m (P.seat (edge x)).1).bits ++
    (J6R20Ancestor.slotWord P (edge x)).bits)=
    side y::((residentPageKey m (P.seat (edge y)).1).bits ++
    (J6R20Ancestor.slotWord P (edge y)).bits) at eq0
  have ee := List.cons.inj eq0
  have E := List.append_inj ee.2 (by rw [(residentPageKey m _).size,(residentPageKey m _).size])
  have pg := resident_page_key_injective m (word_bits_inj E.1)
  have sj := congrArg Word.val (word_bits_inj E.2)
  change (word (q:=a m) (P.seat (edge x)).2.val).val=
    (word (q:=a m) (P.seat (edge y)).2.val).val at sj
  rw [word_val (P.seat (edge x)).2.isLt,word_val (P.seat (edge y)).2.isLt] at sj
  have same : edge x=edge y := P.seat.injective (Prod.ext pg (Fin.ext sj))
  rcases x with (x|x) <;> rcases y with (y|y) <;> simp_all [edge,side]

def makeHalfTape {r c d : ℕ} (m : ℕ) (axis : List Bool) (raw : List (SignedHalfPort r c d)) :
    Meter (List (PortRow (rootHalfWidth m))) :=
  let S := rootSeats m axis raw
  let B := flatMeter (halfPairFee m) (encodeHalfPair m) S.result
  ⟨B.result,S.steps+B.steps+4⟩

def halfTapeFee (m r c d : ℕ) :=
  seatsFee m r c d+M m*(halfPairFee m+halfPairFee m*2+8)+4

theorem actual_root_half_tape {V : Type} [Fintype V] {m n r c d : ℕ} {T : Plant V m n}
    (raw : LiteralPortFile T r c d) (i : Fin (a m)) (axis : List Bool) (clock : axis.length=i.val) :
    let B := makeHalfTape m axis raw.raw
    B.result=(rootHalfOrder m).map (expectedHalfRow T i) ∧ B.result.length=2*M m ∧
      B.steps≤halfTapeFee m r c d := by
  let S := rootSeats m axis raw.raw
  let B := flatMeter (halfPairFee m) (encodeHalfPair m) S.result
  let H (F : SeatField (a m) (pageKeyWidth m)) := [halfPortSpec m false F,halfPortSpec m true F]
  let F := physicalSeatField (rootChart T) i (residentPageKey m)
  obtain ⟨same,Sfee⟩ := root_seat_table_exact raw i axis clock
  obtain ⟨exact,len,paid⟩ := flatMeter_exact (halfPairFee m) (halfPairFee m) 2
    (encodeHalfPair m) H S.result (fun f _=>by rw [half_pair_exact m f]; exact ⟨rfl,le_rfl,rfl⟩)
  have Slen : S.result.length=M m := by rw [show S.result=_ from same,List.length_map,actual_wires_count]
  change B.result=_ ∧ B.result.length=_ ∧ S.steps+B.steps+4≤_
  refine ⟨?_,?_,?_⟩
  · change B.result=_ at exact
    rw [exact,show S.result=_ from same,List.flatMap_map]
    unfold rootHalfOrder
    simp only [SProd.sprod,List.product,List.map_map,List.map_flatMap]
    apply congrArg (fun u : RootWire m→List (PortRow (rootHalfWidth m))=>(actualWires m).flatMap u)
    funext e
    rfl
  · change B.result.length=S.result.length*2 at len
    rw [len,Slen,Nat.mul_comm]
  · change B.steps≤_ at paid
    rw [Slen] at paid
    change S.steps≤_ at Sfee
    unfold halfTapeFee
    omega

#print axioms root_half_order_complete
#print axioms half_addresses_unique
#print axioms actual_root_half_tape
end J6R32RootGeneratedRegistryInputs
