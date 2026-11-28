import J6R14LayoutCostWeave
import J6R14LayoutCostAxes

/-! Decode the paid physical address into the exact P11 Page/Slot type.
The code chooses the constant-zero within-packet convention, which is
allowed by the original packing. The significant orientation bits agree
with the original ordered cell, without using addressInCell's arbitrary
noncomputable enumeration. -/

namespace J6R14LayoutCost
open AOracleMachineTime P11FullPacking

theorem weave_fixed_getD (pick : Bool) (d : Bool×Bool→Bool) (m : AxisMarks)
    (l : List Bool) (i : ℕ) (hi : i<m.length)
    (h : (m.getD i (false,false)).1≠pick) :
    (weave pick d m l).result.1.getD i false=d (m.getD i (false,false)) := by
  induction m generalizing l i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      rw [List.getD_cons_zero] at h
      simp [weave,h]
    | succ i =>
      have ht : i<xs.length := by simpa using hi
      rw [List.getD_cons_succ] at h
      by_cases hx : x.1=pick
      · simpa only [weave,if_pos hx,List.getD_cons_succ] using ih l.tail i ht h
      · simpa only [weave,if_neg hx,List.getD_cons_succ] using ih l i ht h

def marksOf {a : ℕ} (c : Cell (Fin a) (Fin 64)) : AxisMarks :=
  List.ofFn (fun i => (decide ((c i).1≠(c i).2),decide ((c i).2<(c i).1)))

@[simp] theorem marksOf_len {a : ℕ} (c : Cell (Fin a) (Fin 64)) : (marksOf c).length=a :=
  List.length_ofFn

theorem marksOf_at {a : ℕ} (c : Cell (Fin a) (Fin 64)) (i : Fin a) :
    (marksOf c).getD i.val (false,false) =
      (decide ((c i).1≠(c i).2),decide ((c i).2<(c i).1)) := by
  rw [marksOf,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

theorem slotAt_unequal {a : ℕ} (c : Cell (Fin a) (Fin 64)) (r : List Bool)
    (i : Fin a) (h : (c i).1≠(c i).2) :
    (seatWords (marksOf c) r).result.slot.getD i.val false=decide ((c i).2<(c i).1) := by
  change (weave false Prod.snd (marksOf c) r).result.1.getD i.val false=_
  have ht : i.val<(marksOf c).length := by simpa only [marksOf_len] using i.isLt
  rw [weave_fixed_getD false Prod.snd _ _ _ ht (by rw [marksOf_at]; simp [h]),marksOf_at]

noncomputable def decodePhysical {a b : ℕ} (c : Cell (Fin a) (Fin 64)) (s : SeatWords)
    (hb : bitsValue s.page < b) : Physical a b (Fin 64) :=
  let k := key c
  let mask : Orient k := fun i => s.selector.getD i.val.val false
  (⟨k,⟨⟨bitsValue s.page,hb⟩,mask⟩⟩,(bitsChart a).symm (fun j => s.slot.getD j.val false))

theorem realPhysical_single {a b : ℕ} (c : Cell (Fin a) (Fin 64)) (r : List Bool)
    (hwidth : a≤r.length) (hrank : bitsValue r<b*2^a) :
    let p := seatWords (marksOf c) r
    let hb : bitsValue p.result.page<b :=
      page_in_range (marksOf c) r (by rwa [marksOf_len]) b (by rwa [marksOf_len])
    physicalCell (fun _ _ _ => false) (decodePhysical c p.result hb)=c ∧
    p.result.slot.length=a ∧ p.result.selector.length=a ∧ p.steps=16*a+6 := by
  let p := seatWords (marksOf c) r
  have hb : bitsValue p.result.page<b :=
    page_in_range (marksOf c) r (by rwa [marksOf_len]) b (by rwa [marksOf_len])
  obtain ⟨hL,hP,_,_,_,hs⟩ := seatWords_exact (marksOf c) r (by rwa [marksOf_len])
  rw [marksOf_len] at hL hP hs
  refine ⟨?_,hL,hP,hs⟩
  change physicalCell (fun _ _ _ => false) (decodePhysical c p.result hb)=_
  calc
    _ = cell (key c) (orientation c) := by
      change cell (key c) (slotOrient (key c) (fun _ => false)
        ((bitsChart a).symm (fun i => p.result.slot.getD i.val false)))=_
      congr 1
      funext i
      have hneq : (c i.val).1≠(c i.val).2 := by
        intro he
        exact i.property (by simp [key,sortPair,he])
      have hs := slotAt_unequal c r i.val hneq
      change p.result.slot.getD i.val.val false=_ at hs
      have hk := congrFun ((bitsChart a).apply_symm_apply (fun j => p.result.slot.getD j.val false)) i.val
      change bits a ((bitsChart a).symm (fun j => p.result.slot.getD j.val false)) i.val = _ at hk
      rw [slotOrient,shiftMask,hk,hs,orientation]
      cases (decide ((c i.val).2<(c i.val).1)) <;> rfl
    _ = c := cell_decode c

#print axioms weave_fixed_getD
#print axioms marksOf_at
#print axioms realPhysical_single
end J6R14LayoutCost

