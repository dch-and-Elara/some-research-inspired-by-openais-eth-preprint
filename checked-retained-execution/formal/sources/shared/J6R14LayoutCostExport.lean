import J6R14LayoutCostPhysical

/-! Header serialization starts at the raw coordinate words of an
actual ordered-cell bucket. One pass derives comparison flags; a second
pass emits a true physical slot/selector/page using the same flags. -/
namespace J6R14LayoutCost
open AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeLocal P11FullPacking J6R12CollisionEdges

def wordCell {a : ℕ} (c : Cell (Fin a) (Fin 64)) : CellWord :=
  (coordinateLabel (fun i => (c i).1),coordinateLabel (fun i => (c i).2))

def axesOf {a : ℕ} (c : Cell (Fin a) (Fin 64)) : List AxisWord :=
  List.ofFn (fun i => axisSpec (c i).1 (c i).2)

def axisFlag (u : AxisWord) : Bool × Bool := (u.unequal,u.reverse)

theorem markAxes_cell {a : ℕ} (c : Cell (Fin a) (Fin 64)) :
    let t := markAxes a (wordCell c).1 (wordCell c).2
    t.result=axesOf c ∧ t.steps=184*a := by
  have H := markAxes_exact (List.ofFn c)
  rw [List.length_ofFn,List.map_ofFn,List.map_ofFn,List.map_ofFn] at H
  exact H

theorem axes_flags {a : ℕ} (c : Cell (Fin a) (Fin 64)) :
    (axesOf c).map axisFlag=marksOf c := by
  rw [axesOf,List.map_ofFn]
  rfl

def prepareHeader (a : ℕ) (k : CellWord) : Meter (List AxisWord × AxisMarks) :=
  let t := markAxes a k.1 k.2
  let v := mapMeter (fun x => ⟨axisFlag x,8⟩) t.result
  ⟨(t.result,v.result),t.steps+v.steps+8*a+6⟩

def headerCap (a : ℕ) : ℕ := 206*a+6

theorem prepareHeader_exact {a : ℕ} (c : Cell (Fin a) (Fin 64)) :
    let H := prepareHeader a (wordCell c)
    H.result=(axesOf c,marksOf c) ∧ H.steps≤headerCap a := by
  let t := markAxes a (wordCell c).1 (wordCell c).2
  obtain ⟨hr,ht⟩ := markAxes_cell c
  change t.result=axesOf c at hr
  change t.steps=_ at ht
  let v := mapMeter (fun x => ⟨axisFlag x,8⟩) t.result
  obtain ⟨vh,vc⟩ := mapMeter_exact (fun x => ⟨axisFlag x,8⟩)
    axisFlag 8 t.result (fun _ _ => ⟨rfl,le_rfl⟩)
  change v.result=_ at vh
  change v.steps≤_ at vc
  constructor
  · change (t.result,v.result)=_
    rw [vh,hr,axes_flags]
  · change t.steps+v.steps+8*a+6≤_
    rw [ht]
    rw [hr,axesOf,List.length_ofFn] at vc
    unfold headerCap
    omega

structure RawAddress where
  axes : List AxisWord
  flags : AxisMarks
  seat : SeatWords

def exportOne (a : ℕ) (k : CellWord) (r : List Bool) : Meter RawAddress :=
  let h := prepareHeader a k
  let t := seatWords h.result.2 r
  ⟨⟨h.result.1,h.result.2,t.result⟩,h.steps+t.steps+32*a+16⟩

def exportOneCap (a : ℕ) : ℕ := 254*a+28

theorem exportOne_exact {a pages : ℕ} (c : Cell (Fin a) (Fin 64))
    (r : List Bool) (hw : a≤r.length) (hr : bitsValue r<pages*2^a) :
    let x := exportOne a (wordCell c) r
    ∃ hp : bitsValue x.result.seat.page<pages,
      x.result.axes=axesOf c ∧ x.result.flags=marksOf c ∧
      physicalCell (fun _ _ _ => false) (decodePhysical c x.result.seat hp)=c ∧
      selectMask false x.result.flags x.result.seat.slot++
        selectMask true x.result.flags x.result.seat.selector++x.result.seat.page=r ∧
      x.steps≤exportOneCap a := by
  let h := prepareHeader a (wordCell c)
  obtain ⟨hR,hC⟩ := prepareHeader_exact c
  change h.result=_ at hR
  change h.steps≤_ at hC
  have h₁ : h.result.1=axesOf c := congrArg Prod.fst hR
  have h₂ : h.result.2=marksOf c := congrArg Prod.snd hR
  let t := seatWords (marksOf c) r
  have hseat : (seatWords h.result.2 r).result=t.result := by rw [h₂]
  have hts : (seatWords h.result.2 r).steps=16*a+6 := by
    rw [h₂,(seatWords_exact (marksOf c) r (by rwa [marksOf_len])).2.2.2.2.2,marksOf_len]
  have hb : bitsValue t.result.page<pages :=
    page_in_range (marksOf c) r (by rwa [marksOf_len]) pages (by rwa [marksOf_len])
  have hb' : bitsValue (exportOne a (wordCell c) r).result.seat.page<pages := by
    change bitsValue (seatWords h.result.2 r).result.page<pages
    rwa [hseat]
  refine ⟨hb',h₁,h₂,?_,?_,?_⟩
  · change physicalCell _ (decodePhysical c (seatWords h.result.2 r).result hb')=_
    simpa only [h₂] using (realPhysical_single c r hw hr).1
  · change selectMask false h.result.2 (seatWords h.result.2 r).result.slot++
      selectMask true h.result.2 (seatWords h.result.2 r).result.selector++
      (seatWords h.result.2 r).result.page=_
    rw [h₂]
    exact (seatWords_exact (marksOf c) r (by rwa [marksOf_len])).2.2.2.1
  · change h.steps+(seatWords h.result.2 r).steps+32*a+16≤_
    rw [hts]
    unfold headerCap at hC
    unfold exportOneCap
    omega

#print axioms markAxes_cell
#print axioms axes_flags
#print axioms prepareHeader_exact
#print axioms exportOne_exact
end J6R14LayoutCost



