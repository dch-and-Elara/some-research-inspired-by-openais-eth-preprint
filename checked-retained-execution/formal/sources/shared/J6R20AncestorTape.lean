import J6R19RetainedFrames
import J6R18ChildWriteOperands

/-! A one-hop descendant port has a new left tag, the ancestor packet
right tag, then its original slot side/address. Read those literal tags
and join by a metered equality scan, not a prebuilt permutation. -/
namespace J6R20Ancestor
open AOracleMachineTime AOracleMachineTimeTape A1R9 A1R12 J6R18ChildWrite
open J6R15ModeCost J6R19Retained J6R12CollisionMenu

structure Key (a : ℕ) where
  side : Bool
  slot : Word a

abbrev Raw := List Bool × Bool

private theorem bits_inj {a : ℕ} : Function.Injective (fun x : Word a=>x.bits) := by
  rintro ⟨x,hx⟩ ⟨y,hy⟩ h
  have H : x=y := h
  subst y
  rfl

def nested {a : ℕ} (e : Key a × Bool) : Raw :=
  (false::true::e.1.side::e.1.slot.bits,e.2)

def readPort (a : ℕ) : Raw→Meter (Option (Key a × Bool))
  | (false::true::s::bits,b) =>
    let t := scanWidth a bits
    let w : Word a := ⟨t.result,
      (congrArg List.length (scanWidth_exact a bits).1).trans (lowBits_len a bits)⟩
    ⟨some (⟨s,w⟩,b),t.steps+8⟩
  | _ => ⟨none,8⟩

def portFee (a : ℕ) := 4*a+9

theorem readPort_exact {a : ℕ} (k : Key a) (b : Bool) :
    (readPort a (nested (k,b))).result=some (k,b) ∧
      (readPort a (nested (k,b))).steps=portFee a := by
  obtain ⟨hs,hc⟩ := scanWidth_exact a k.slot.bits
  have H : lowBits a k.slot.bits=k.slot.bits := by
    simpa only [List.append_nil,k.slot.size] using lowBits_prefix k.slot.bits []
  have hW : (⟨(scanWidth a k.slot.bits).result,
      (congrArg List.length hs).trans (lowBits_len a k.slot.bits)⟩ : Word a)=k.slot := by
    exact bits_inj (hs.trans H)
  refine ⟨?_,?_⟩
  · cases k with
    | mk s w => change some (Key.mk s _,b)=some (Key.mk s w,b); rw [hW]
  · change (scanWidth a k.slot.bits).steps+8=_
    rw [hc,portFee]

def readTape (a : ℕ) : List Raw→Meter (List (Key a × Bool))
  | [] => ⟨[],2⟩
  | r::rs =>
    let h := readPort a r
    let z := readTape a rs
    ⟨h.result.elim z.result (fun x=>x::z.result),h.steps+z.steps+a+8⟩

def tapeFee (a n : ℕ) := n*(portFee a+a+8)+2

theorem readTape_exact {a : ℕ} (l : List (Key a × Bool)) :
    readTape a (l.map nested)=⟨l,tapeFee a l.length⟩ := by
  induction l with
  | nil => simp [readTape,tapeFee]
  | cons x xs ih =>
    obtain ⟨k,b⟩ := x
    obtain ⟨h,c⟩ := readPort_exact k b
    simp only [List.map_cons,readTape,h,c,ih,Option.elim_some,List.length_cons,tapeFee]
    congr 1
    rw [Nat.succ_mul xs.length]
    omega

def compare {a : ℕ} (x y : Key a) : Meter Bool :=
  let d := eqWord x.slot.bits y.slot.bits
  ⟨(x.side==y.side) && d.result,d.steps+5⟩

theorem compare_exact {a : ℕ} (x y : Key a) :
    ((compare x y).result=true ↔ x=y) ∧ (compare x y).steps=10*a+5 := by
  have hL := x.slot.size.trans y.slot.size.symm
  obtain ⟨he,hc⟩ := eqWord_exact x.slot.bits y.slot.bits hL
  constructor
  · change ((x.side==y.side) && (eqWord x.slot.bits y.slot.bits).result)=true ↔ _
    rw [Bool.and_eq_true,beq_iff_eq,he]
    constructor
    · rintro ⟨h,e⟩
      have hs := equal_width_inj hL e
      have hw : x.slot=y.slot := bits_inj hs
      cases x
      cases y
      simp_all
    · intro h; subst y; exact ⟨rfl,rfl⟩
  · change (eqWord x.slot.bits y.slot.bits).steps+5=_
    rw [hc,x.slot.size]

def findBit {a : ℕ} (k : Key a) : List (Key a×Bool)→Meter Bool
  | [] => ⟨false,2⟩
  | (x,b)::xs =>
    let c := compare k x
    let fee := c.steps+a+8
    if c.result then ⟨b,fee⟩
    else
      let d := findBit k xs
      ⟨d.result,fee+d.steps⟩

def findFee (a n : ℕ) := n*(11*a+13)+2

theorem findBit_correct {a : ℕ} (k : Key a) (b : Bool) (xs : List (Key a×Bool))
    (here : (k,b)∈xs) (unique : ∀ z,(k,z)∈xs → z=b) :
    (findBit k xs).result=b := by
  induction xs with
  | nil => simp at here
  | cons x xs ih =>
    obtain ⟨v,c⟩ := x
    by_cases h : k=v
    · subst v
      have hu := unique c List.mem_cons_self
      unfold findBit
      rw [if_pos ((compare_exact k k).1.mpr rfl)]
      exact hu
    · have ha : (k,b)∈xs := by
        rcases List.mem_cons.mp here with e | e
        · exact (h (congrArg Prod.fst e)).elim
        · exact e
      have hd := ih ha (fun z hz=>unique z (List.mem_cons_of_mem _ hz))
      unfold findBit
      rw [if_neg (fun e=>h ((compare_exact k v).1.mp e))]
      exact hd

theorem findBit_cost {a : ℕ} (k : Key a) (xs : List (Key a×Bool)) :
    (findBit k xs).steps≤findFee a xs.length := by
  induction xs with
  | nil => simp [findBit,findFee]
  | cons x xs ih =>
    obtain ⟨v,c⟩ := x
    have h : (compare k v).steps+a+8=11*a+13 := by rw [(compare_exact k v).2]; omega
    rw [findBit]
    change (findBit k xs).steps≤xs.length*(11*a+13)+2 at ih
    split
    · change (compare k v).steps+a+8≤(xs.length+1)*(11*a+13)+2
      rw [h,Nat.succ_mul xs.length]
      omega
    · change (compare k v).steps+a+8+(findBit k xs).steps≤(xs.length+1)*(11*a+13)+2
      rw [h,Nat.succ_mul xs.length]
      omega

def fillSlots {a : ℕ} (s : Bool) (xs : List (Key a×Bool))
    (slots : List (Word a)) : Meter (List (SlotBit a)) :=
  mapMeter (fun w=>let z:=findBit ⟨s,w⟩ xs; ⟨⟨w,z.result⟩,z.steps⟩) (a+1) slots

def slotFee (a n r : ℕ) := r*(findFee a n+a+5)

theorem fillSlots_exact {a : ℕ} (s : Bool) (xs : List (Key a×Bool))
    (slots : List (Word a)) (value : Word a→Bool)
    (h : ∀ w∈slots, (⟨s,w⟩,value w)∈xs ∧
      ∀ z,(⟨s,w⟩,z)∈xs → z=value w) :
    (fillSlots s xs slots).result=slots.map (fun w=>⟨w,value w⟩) ∧
      (fillSlots s xs slots).steps≤slotFee a xs.length slots.length := by
  obtain ⟨hv,hc⟩ := mapMeter_exact (fun w : Word a=>let z:=findBit ⟨s,w⟩ xs; ⟨⟨w,z.result⟩,z.steps⟩ :
      Word a→Meter (SlotBit a)) (a+1) (findFee a xs.length) slots (fun w _=>findBit_cost ⟨s,w⟩ xs)
  constructor
  · unfold fillSlots
    rw [hv]
    apply List.map_congr_left
    intro w hm
    obtain ⟨hp,hu⟩ := h w hm
    change SlotBit.mk w (findBit ⟨s,w⟩ xs).result=SlotBit.mk w (value w)
    rw [findBit_correct _ _ _ hp hu]
  · change (fillSlots s xs slots).steps≤_
    unfold fillSlots slotFee
    exact hc.trans (Nat.mul_le_mul_left _ (by omega))

#print axioms readPort_exact
#print axioms readTape_exact
#print axioms compare_exact
#print axioms findBit_correct
#print axioms findBit_cost
#print axioms fillSlots_exact
end J6R20Ancestor



