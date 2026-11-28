import J6R14LayoutCostTags

/-! Every ordered binary key is enumerated in tape-lexicographic order.
Within a key the edge occurrence order is unchanged. The maximum is
computed from fixed-width counters, not a semantic maxFiber oracle. -/

namespace J6R14LayoutCost
open AOracleMachineTime AOracleMachineTimeTape AOracleMachineTimeLocal
open J6R12CollisionBits J6R12CollisionEdges J6R12CollisionMenu

def pairsSpec (left right : List (List Bool)) : List CellWord :=
  left.flatMap (fun x => right.map (fun y => (x,y)))

def pairMenu (b : ℕ) (right : List (List Bool)) : List (List Bool) → Meter (List CellWord)
  | [] => ⟨[],0⟩
  | x::xs =>
    let a := mapMeter (fun y => ⟨(x,y),4*b+8⟩) right
    let t := pairMenu b right xs
    ⟨a.result++t.result,a.steps+t.steps+(4*b+8)*right.length+4⟩

theorem pairMenu_exact (b : ℕ) (left right : List (List Bool)) :
    (pairMenu b right left).result=pairsSpec left right ∧
    (pairMenu b right left).steps≤left.length*((8*b+22)*right.length+4) := by
  induction left with
  | nil => simp [pairMenu,pairsSpec]
  | cons x xs ih =>
    let a := mapMeter (fun y => ⟨(x,y),4*b+8⟩) right
    let t := pairMenu b right xs
    have H := mapMeter_exact (fun y : List Bool => ⟨(x,y),4*b+8⟩)
      (fun y => (x,y)) (4*b+8) right (fun _ _ => ⟨rfl,le_rfl⟩)
    change a.result=right.map _ ∧ a.steps≤_ at H
    refine ⟨?_,?_⟩
    · change a.result++t.result=_
      rw [H.1,ih.1]
      rfl
    · change a.steps+t.steps+(4*b+8)*right.length+4≤(xs.length+1)*_
      rw [Nat.succ_mul xs.length]
      have hW : (4*b+8+6)*right.length+(4*b+8)*right.length = (8*b+22)*right.length := by ring
      have ht := ih.2
      change t.steps≤_ at ht
      omega

theorem pairsSpec_length (left right : List (List Bool)) :
    (pairsSpec left right).length=left.length*right.length := by
  induction left with
  | nil => simp [pairsSpec]
  | cons x xs ih =>
    simp [pairsSpec] at ih
    simp [pairsSpec,Nat.succ_mul,Nat.add_comm]

theorem pairsSpec_mem (left right : List (List Bool)) (k : CellWord) :
    k∈pairsSpec left right ↔ k.1∈left ∧ k.2∈right := by
  cases k
  simp [pairsSpec,List.mem_flatMap,List.mem_map,and_left_comm]

theorem pairsSpec_nodup (left right : List (List Bool)) (hl : left.Nodup) (hr : right.Nodup) :
    (pairsSpec left right).Nodup := by
  induction left with
  | nil => simp [pairsSpec]
  | cons x xs ih =>
    obtain ⟨hx,hs⟩ := List.nodup_cons.mp hl
    change ((right.map (fun y => (x,y))) ++ pairsSpec xs right).Nodup
    rw [List.nodup_append]
    refine ⟨hr.map (fun _ _ h => congrArg Prod.snd h),ih hs,?_⟩
    intro p hp q hq hpq
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hp
    subst q
    exact hx ((pairsSpec_mem xs right (x,v)).mp hq).1

def maxWord (q : ℕ) (a b : List Bool) : Meter (List Bool) :=
  let s := compareBits a b
  ⟨if s.result then b else a,s.steps+4*q+4⟩

theorem maxWord_exact (q : ℕ) (a b : List Bool) (ha : a.length=q) (hb : b.length=q) :
    (maxWord q a b).result.length=q ∧
    bitsValue (maxWord q a b).result=max (bitsValue a) (bitsValue b) ∧
    (maxWord q a b).steps=14*q+4 := by
  let s := compareBits a b
  obtain ⟨hv,hc⟩ := compareBits_exact a b (ha.trans hb.symm)
  change (s.result=true ↔ _) at hv
  change s.steps=_ at hc
  rw [ha] at hc
  by_cases h : bitsValue a<bitsValue b
  · have hs : s.result=true := hv.mpr h
    simp [maxWord,show (compareBits a b).result=true from hs,hb,max_eq_right h.le]
    change s.steps+4*q=14*q
    omega
  · have hs : s.result=false := Bool.eq_false_iff.mpr (fun H => h (hv.mp H))
    simp [maxWord,show (compareBits a b).result=false from hs,ha,max_eq_left (Nat.le_of_not_gt h)]
    change s.steps+4*q=14*q
    omega

structure Box (X : Type*) where
  key : CellWord
  rows : List X
  count : List Bool

def boxSpec {X : Type*} (view : X→EdgeTape) (q : ℕ) (es : List X) (k : CellWord) : Box X :=
  ⟨k,bucket view k es,encodeBits q (bucket view k es).length⟩

def boxStepCap (kR kC b q M : ℕ) : ℕ :=
  q+2+M*scanStepCap kR kC b q+14*q+4+4*b+2*q+8

def groupAll {X : Type*} (view : X→EdgeTape) (kR kC b q : ℕ) (es : List X) :
    List CellWord → Meter (List (Box X) × List Bool)
  | [] => ⟨([],List.replicate q false),q+2⟩
  | k::ks =>
    let x := groupOne view kR kC b q k es
    let t := groupAll view kR kC b q es ks
    let v := maxWord q x.result.2 t.result.2
    ⟨(⟨k,x.result.1,x.result.2⟩::t.result.1,v.result),x.steps+t.steps+v.steps+4*b+2*q+8⟩

def peak {X : Type*} (view : X→EdgeTape) (es : List X) (ks : List CellWord) : ℕ :=
  ks.foldr (fun k m => max (bucket view k es).length m) 0

theorem groupAll_exact {X : Type*} (view : X→EdgeTape) (kR kC b q : ℕ) (hq : 0<q)
    (es : List X) (hf : es.length<2^q) (he : ∀ e∈es,labelWidths b (view e))
    (ks : List CellWord) (hw : ∀ k∈ks,k.1.length=b ∧ k.2.length=b) :
    let u := groupAll view kR kC b q es ks
    u.result.1=ks.map (boxSpec view q es) ∧ u.result.2.length=q ∧
    bitsValue u.result.2=peak view es ks ∧
      u.steps≤q+2+ks.length*boxStepCap kR kC b q es.length := by
  induction ks with
  | nil => simp [groupAll,peak,AOracleMachineTimeMul.value_zero]
  | cons k ks ih =>
    obtain ⟨hL,hR⟩ := hw k List.mem_cons_self
    let x := groupOne view kR kC b q k es
    let t := groupAll view kR kC b q es ks
    let v := maxWord q x.result.2 t.result.2
    obtain ⟨xr,xw,xn,xc⟩ := groupOne_exact view kR kC b q hq k es hL hR hf he
    obtain ⟨tr,tw,tn,tc⟩ := ih (fun x hx => hw x (List.mem_cons_of_mem _ hx))
    have hi : (bucket view k es).length<2^q := (List.length_filter_le ..).trans_lt hf
    have xe : x.result.2=encodeBits q (bucket view k es).length := by
      apply equal_width_inj (xw.trans (encodeBits_length _ _).symm)
      exact xn.trans (encodeBits_exact _ _ hi).symm
    obtain ⟨vl,vn,vc⟩ := maxWord_exact q x.result.2 t.result.2 xw tw
    refine ⟨?_,vl,?_,?_⟩
    · change (Box.mk k x.result.1 x.result.2 :: t.result.1)=_
      rw [show x.result.1=_ from xr,xe,show t.result.1=_ from tr]
      rfl
    · change bitsValue v.result=max (bucket view k es).length (peak view es ks)
      rw [show bitsValue v.result=_ from vn,show bitsValue x.result.2=_ from xn,
        show bitsValue t.result.2=_ from tn]
    · change x.steps+t.steps+v.steps+4*b+2*q+8≤_
      rw [List.length_cons,Nat.succ_mul ks.length]
      change x.steps≤_ at xc
      change t.steps≤_ at tc
      change v.steps=_ at vc
      unfold boxStepCap at tc ⊢
      omega

theorem peak_le {X : Type*} (view : X→EdgeTape) (es : List X) (ks : List CellWord) (H : ℕ)
    (h : ∀ k∈ks,(bucket view k es).length≤H) : peak view es ks≤H := by
  induction ks with
  | nil => exact Nat.zero_le _
  | cons k ks ih =>
    exact max_le (h k List.mem_cons_self) (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem bucket_le_peak {X : Type*} (view : X→EdgeTape) (es : List X) (ks : List CellWord)
    (k : CellWord) (hk : k∈ks) : (bucket view k es).length≤peak view es ks := by
  induction ks with
  | nil => simp at hk
  | cons x xs ih =>
    rcases List.mem_cons.mp hk with rfl|ht
    · exact le_max_left _ _
    · exact (ih ht).trans (le_max_right _ _)

#print axioms pairMenu_exact
#print axioms pairsSpec_nodup
#print axioms groupAll_exact
#print axioms peak_le
#print axioms bucket_le_peak
end J6R14LayoutCost

