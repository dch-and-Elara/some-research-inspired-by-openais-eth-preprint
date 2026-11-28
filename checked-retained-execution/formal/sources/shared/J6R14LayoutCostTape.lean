import J6R14LayoutCostBox
import Mathlib.Data.List.Forall2

/-! Sequential serialization of every actual ordered group. Reading
each header and emitting its whole real-edge record tape are charged. -/
namespace J6R14LayoutCost
open AOracleMachineTime AOracleMachineTimeTape P11FullPacking

def boxFaithful (a pages q : ℕ) (B : Box Tagged) (x : ExportBox) : Prop :=
  x.key=B.key ∧ x.rows.map Seated.tag=B.rows ∧
  ∃ c : Cell (Fin a) (Fin 64), B.key=wordCell c ∧
    x.axes=axesOf c ∧ x.flags=marksOf c ∧
    ∀ i : Fin B.rows.length, ∃ t,
      x.rows[i.val]?=some t ∧ t.tag=B.rows[i] ∧
      rawCell t.tag.edge=some B.key ∧
      t.address=(seatWords (marksOf c) (encodeBits q i.val)).result ∧
      ∃ hp : bitsValue t.address.page<pages,
        physicalCell (fun _ _ _ => false) (decodePhysical c t.address hp)=c

def rowsOnTape (bs : List (Box Tagged)) : ℕ := (bs.flatMap Box.rows).length

def exportTape (kR kC b q a : ℕ) : List (Box Tagged) → Meter (List ExportBox)
  | [] => ⟨[],0⟩
  | B::bs =>
    let e := exportBox kR kC b q a B
    let t := exportTape kR kC b q a bs
    ⟨e.result::t.result,e.steps+t.steps+6⟩

def exportTapeCap (kR kC b q a boxes records : ℕ) : ℕ :=
  boxes*(headerCap a+2*b+q+18)+records*seatStepCap kR kC b q a

theorem exportTape_exact (kR kC b q a pages : ℕ) (hq : 0<q) (ha : a≤q)
    (bs : List (Box Tagged)) (H : ∀ B∈bs,validBox a pages q B) :
    let t := exportTape kR kC b q a bs
    List.Forall₂ (boxFaithful a pages q) bs t.result ∧
    t.steps≤exportTapeCap kR kC b q a bs.length (rowsOnTape bs) := by
  induction bs with
  | nil => simp [exportTape,exportTapeCap,rowsOnTape]
  | cons B bs ih =>
    let e := exportBox kR kC b q a B
    let t := exportTape kR kC b q a bs
    obtain ⟨hk,hrows,hf,ht⟩ := exportBox_exact kR kC b q a pages hq ha B (H _ List.mem_cons_self)
    obtain ⟨hP,hC⟩ := ih (fun _ hr => H _ (List.mem_cons_of_mem _ hr))
    change e.steps≤_ at ht
    change t.steps≤_ at hC
    refine ⟨.cons ⟨hk,hrows,hf⟩ hP,?_⟩
    change e.steps+t.steps+6≤_
    have hcount : rowsOnTape (B::bs)=B.rows.length+rowsOnTape bs := by
      simp [rowsOnTape]
    rw [hcount,List.length_cons]
    unfold exportBoxCap at ht
    unfold exportTapeCap at hC ⊢
    rw [Nat.succ_mul bs.length,Nat.add_mul]
    omega

theorem exportTape_conserves {a pages q : ℕ} {bs : List (Box Tagged)} {outs : List ExportBox}
    (h : List.Forall₂ (boxFaithful a pages q) bs outs) :
    outs.flatMap (fun x => x.rows.map Seated.tag)=bs.flatMap Box.rows := by
  induction h with
  | nil => rfl
  | cons hL _ ih =>
    rw [List.flatMap_cons,List.flatMap_cons,hL.2.1,ih]

#print axioms exportTape_exact
#print axioms exportTape_conserves
end J6R14LayoutCost



