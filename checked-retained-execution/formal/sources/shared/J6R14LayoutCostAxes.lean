import J6R14LayoutCostGroup
import P11FullPackingChart

/-! Canonical coordinatewise type/orientation decoder for the source
alphabet Fin 64. It scans two raw words in six-bit chunks, pays both
comparisons and copies, and outputs the actual ordered-symbol key
with one hot bit and one orientation bit per coordinate. -/

namespace J6R14LayoutCost
open AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeLocal
open J6R12CollisionBits J6R12CollisionMenu J6R12CollisionGreedyStep P11FullPacking

structure AxisWord where
  low : List Bool
  high : List Bool
  unequal : Bool
  reverse : Bool

def symbol (x : Fin 64) : List Bool := encodeBits 6 x.val

theorem symbol_length (x : Fin 64) : (symbol x).length=6 := encodeBits_length _ _

theorem symbol_value (x : Fin 64) : bitsValue (symbol x)=x.val := encodeBits_exact _ _ x.isLt

def axisSpec (x y : Fin 64) : AxisWord :=
  ⟨symbol (sortPair (x,y)).1,symbol (sortPair (x,y)).2,decide (x≠y),decide (y<x)⟩

def sortAxis (l r : List Bool) : Meter AxisWord :=
  let t := compareBits r l
  let e := sameBits l r
  ⟨⟨if t.result then r else l,if t.result then l else r,!e.result,t.result⟩,t.steps+e.steps+32⟩

theorem sortAxis_exact (x y : Fin 64) :
    (sortAxis (symbol x) (symbol y)).result=axisSpec x y ∧
    (sortAxis (symbol x) (symbol y)).steps=152 := by
  let t := compareBits (symbol y) (symbol x)
  let e := sameBits (symbol x) (symbol y)
  obtain ⟨ht,htc⟩ := compareBits_exact (symbol y) (symbol x) (by rw [symbol_length,symbol_length])
  obtain ⟨he,hec⟩ := sameBits_exact (symbol x) (symbol y) (by rw [symbol_length,symbol_length])
  rw [symbol_value,symbol_value] at ht he
  have Ht : t.result=decide (y<x) := by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    exact ht
  have He : e.result=decide (x=y) := by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    exact he.trans Fin.ext_iff.symm
  have hh : t.steps=60 := by rw [show t.steps=_ from htc,symbol_length]
  have hE : e.steps=60 := by rw [show e.steps=_ from hec,symbol_length]
  refine ⟨?_,?_⟩
  · change AxisWord.mk (if t.result then _ else _) (if t.result then _ else _) (!e.result) t.result=_
    rw [Ht,He]
    by_cases h : y<x
    · simp [axisSpec,sortPair,h,not_le_of_gt h,ne_of_gt h]
    · by_cases k : x=y <;> simp [axisSpec,sortPair,h,k,le_of_not_gt h]
  · change t.steps+e.steps+32=_
    rw [hh,hE]

def symbolTape (l : List (Fin 64)) : List Bool := l.flatMap symbol

theorem symbolTape_length (l : List (Fin 64)) : (symbolTape l).length=6*l.length := by
  induction l with
  | nil => simp [symbolTape]
  | cons x xs ih =>
    change (symbol x++symbolTape xs).length=_
    rw [List.length_append,symbol_length,ih,List.length_cons,Nat.mul_succ]
    omega

theorem symbol_take_append (x : Fin 64) (u : List Bool) :
    (symbol x++u).take 6=symbol x := by
  rw [← symbol_length x,List.take_left]

theorem symbol_drop_append (x : Fin 64) (u : List Bool) :
    (symbol x++u).drop 6=u := by
  rw [← symbol_length x,List.drop_left]

theorem symbolTape_inj : Function.Injective symbolTape := by
  intro l r H
  induction l generalizing r with
  | nil =>
    have h := congrArg List.length H
    rw [symbolTape_length,symbolTape_length,List.length_nil] at h
    exact (List.length_eq_zero_iff.mp (by omega : r.length=0)).symm
  | cons x xs ih =>
    cases r with
    | nil =>
      have h := congrArg List.length H
      rw [symbolTape_length,symbolTape_length,List.length_nil,List.length_cons] at h
      omega
    | cons y ys =>
      change symbol x++symbolTape xs=symbol y++symbolTape ys at H
      have h := congrArg (fun l : List Bool => l.take 6) H
      dsimp only at h
      rw [symbol_take_append,symbol_take_append] at h
      have t := congrArg (fun l : List Bool => l.drop 6) H
      dsimp only at t
      rw [symbol_drop_append,symbol_drop_append] at t
      have he := congrArg bitsValue h
      rw [symbol_value,symbol_value] at he
      rw [Fin.ext he,ih t]

def coordinateLabel {a : ℕ} (f : Fin a→Fin 64) : List Bool := symbolTape (List.ofFn f)

theorem coordinateLabel_len {a : ℕ} (f : Fin a→Fin 64) : (coordinateLabel f).length=6*a := by
  rw [coordinateLabel,symbolTape_length,List.length_ofFn]

theorem coordinateLabel_inj {a : ℕ} : Function.Injective (@coordinateLabel a) := by
  intro x y h
  exact List.ofFn_injective (symbolTape_inj h)

def physicalFormat {E R C : Type*} [Fintype E] {a : ℕ}
    (F : Format E R C (Fin a→Fin 64)) (hb : F.b=6*a) : Format E R C (Fin a→Fin 64) :=
  { F with
    aCode := fun x => bitsValue (coordinateLabel x)
    aInj := by
      intro x y H
      apply coordinateLabel_inj
      apply equal_width_inj (by rw [coordinateLabel_len,coordinateLabel_len])
      exact H
    aFit := fun x => by rw [hb,← coordinateLabel_len x]; exact bitsValue_lt _ }

theorem physicalFormat_label {E R C : Type*} [Fintype E] {a : ℕ}
    (F : Format E R C (Fin a→Fin 64)) (hb : F.b=6*a) (x : Fin a→Fin 64) :
    (physicalFormat F hb).label x=coordinateLabel x := by
  apply equal_width_inj
  · change (encodeBits F.b (bitsValue (coordinateLabel x))).length=_
    rw [encodeBits_length,hb,coordinateLabel_len]
  · change bitsValue (encodeBits F.b (bitsValue (coordinateLabel x)))=_
    exact encodeBits_exact _ _ ((physicalFormat F hb).aFit x)

def markAxes : ℕ → List Bool → List Bool → Meter (List AxisWord)
  | 0,_,_ => ⟨[],0⟩
  | a+1,l,r =>
    let t := sortAxis (l.take 6) (r.take 6)
    let u := markAxes a (l.drop 6) (r.drop 6)
    ⟨t.result::u.result,t.steps+u.steps+32⟩

theorem markAxes_exact (p : List (Fin 64×Fin 64)) :
    let t := markAxes p.length (symbolTape (p.map Prod.fst)) (symbolTape (p.map Prod.snd))
    t.result=p.map (fun q => axisSpec q.1 q.2) ∧ t.steps=184*p.length := by
  induction p with
  | nil => simp [markAxes]
  | cons x xs ih =>
    have h₁ : symbolTape ((x::xs).map Prod.fst)=symbol x.1++symbolTape (xs.map Prod.fst) := rfl
    have h₂ : symbolTape ((x::xs).map Prod.snd)=symbol x.2++symbolTape (xs.map Prod.snd) := rfl
    obtain ⟨hs,hc⟩ := sortAxis_exact x.1 x.2
    obtain ⟨hr,ht⟩ := ih
    dsimp only
    rw [h₁,h₂,List.length_cons]
    simp only [markAxes,symbol_take_append,symbol_drop_append,hs,hc,hr,ht,List.map_cons,Nat.mul_succ,
      true_and]
    omega

#print axioms sortAxis_exact
#print axioms symbolTape_inj
#print axioms physicalFormat_label
#print axioms markAxes_exact
end J6R14LayoutCost


