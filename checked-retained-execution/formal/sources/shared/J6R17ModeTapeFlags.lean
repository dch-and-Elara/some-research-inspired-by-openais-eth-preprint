import J6R14LayoutCostGreedy
import J6R16ModeCostCatalog

/-! Read the actual R14 packet header tape. The raw ordered cell
codes both the sorted key and its orientation selector. The selector
is part of a real Page, so one must keep all eligible orientations. -/
namespace J6R17ModeTape
open AOracleMachineTime AOracleMachineTimeTape J6R14LayoutCost P11FullPacking
open J6R12CollisionEdges

def noReverse : AxisMarks → Meter Bool
  | [] => ⟨true,4⟩
  | (_,b)::xs =>
    let z := noReverse xs
    ⟨(!b && z.result),z.steps+8⟩

theorem noReverse_exact (xs : AxisMarks) :
    ((noReverse xs).result=true ↔ ∀ x∈xs,x.2=false) ∧
      (noReverse xs).steps=8*xs.length+4 := by
  induction xs with
  | nil => simp [noReverse]
  | cons x xs ih =>
    rcases x with ⟨b,v⟩
    simp [noReverse,ih.1,ih.2,Nat.mul_succ,Nat.add_comm,Nat.add_left_comm]

def selectedHot : ℕ → AxisMarks → Meter Bool
  | _,[] => ⟨false,4⟩
  | 0,(b,_)::_ => ⟨b,8⟩
  | i+1,_::xs =>
    let z := selectedHot i xs
    ⟨z.result,z.steps+8⟩

theorem selectedHot_exact (i : ℕ) (xs : AxisMarks) :
    (selectedHot i xs).result=(xs[i]?.map Prod.fst).getD false := by
  induction i generalizing xs with
  | zero => cases xs <;> rfl
  | succ i ih => cases xs with
    | nil => rfl
    | cons x xs =>
      change (selectedHot i xs).result=(xs[i]?.map Prod.fst).getD false
      exact ih xs

theorem selectedHot_fee (i : ℕ) (xs : AxisMarks) :
    (selectedHot i xs).steps≤8*xs.length+4 := by
  induction xs generalizing i with
  | nil => simp [selectedHot]
  | cons x xs ih =>
    cases i with
    | zero => cases x; simp [selectedHot,Nat.mul_succ]
    | succ i =>
      have H := ih i
      change (selectedHot i xs).steps+8≤8*(xs.length+1)+4
      rw [Nat.mul_succ]
      omega

abbrev Header := CellWord × AxisMarks

def encodeHeader {a : ℕ} (c : Cell (Fin a) (Fin 64)) : Header :=
  (wordCell c,marksOf c)

def keepHeader (i : ℕ) (h : Header) : Meter Bool :=
  selectedHot i h.2

theorem keepHeader_exact {a : ℕ} (i : Fin a) (c : Cell (Fin a) (Fin 64)) :
    ((keepHeader i.val (encodeHeader c)).result=true ↔
      (c i).1≠(c i).2) ∧
    (keepHeader i.val (encodeHeader c)).steps≤8*a+4 := by
  have hb := selectedHot_exact i.val (marksOf c)
  have hL : i.val<(marksOf c).length := by rw [marksOf_len]; exact i.isLt
  have hB := selectedHot_fee i.val (marksOf c)
  rw [marksOf_len] at hB
  have hH : (selectedHot i.val (marksOf c)).result=decide ((c i).1≠(c i).2) := by
    rw [hb]
    have H := marksOf_at c i
    rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hL] at H
    rw [List.getElem?_eq_getElem hL]
    exact congrArg Prod.fst H
  exact ⟨by simp only [keepHeader,encodeHeader,hH,decide_eq_true_eq],hB⟩

def keptKeys (a i : ℕ) : List Header → Meter (List CellWord)
  | [] => ⟨[],0⟩
  | x::xs =>
    let h := keepHeader i x
    let z := keptKeys a i xs
    ⟨if h.result then x.1::z.result else z.result,h.steps+z.steps+24*a+12⟩

def crossingSpec {a : ℕ} (i : Fin a) (c : Cell (Fin a) (Fin 64)) : Bool :=
  decide ((c i).1≠(c i).2)

theorem keptKeys_exact {a : ℕ} (i : Fin a) (cs : List (Cell (Fin a) (Fin 64))) :
    let z := keptKeys a i.val (cs.map encodeHeader)
    z.result=(cs.filter (crossingSpec i)).map wordCell ∧
    z.steps≤(32*a+16)*cs.length := by
  induction cs with
  | nil => simp [keptKeys]
  | cons c cs ih =>
    obtain ⟨h,hc⟩ := keepHeader_exact i c
    have he : (keepHeader i.val (encodeHeader c)).result=crossingSpec i c := by
      apply Bool.eq_iff_iff.mpr
      simpa [crossingSpec] using h
    let z := keptKeys a i.val (cs.map encodeHeader)
    change z.result=_ ∧ z.steps≤_ at ih
    refine ⟨?_,?_⟩
    · change (if (keepHeader i.val (encodeHeader c)).result then (wordCell c)::z.result else z.result)=_
      rw [he,ih.1]
      cases hB : crossingSpec i c <;> simp [hB]
    · change (keepHeader i.val (encodeHeader c)).steps+z.steps+24*a+12≤(32*a+16)*(cs.length+1)
      rw [Nat.mul_succ]
      omega

theorem wordCell_injective (a : ℕ) :
    Function.Injective (@wordCell a) := by
  intro c d h
  have h₁ := coordinateLabel_inj (congrArg Prod.fst h)
  have h₂ := coordinateLabel_inj (congrArg Prod.snd h)
  funext k
  exact Prod.ext (congrFun h₁ k) (congrFun h₂ k)

#print axioms noReverse_exact
#print axioms selectedHot_exact
#print axioms selectedHot_fee
#print axioms keepHeader_exact
#print axioms keptKeys_exact
#print axioms wordCell_injective
end J6R17ModeTape



