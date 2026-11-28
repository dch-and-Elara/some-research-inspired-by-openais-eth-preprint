import J6R14LayoutCostWeave
import J6R14LayoutCostTags

/-! The q-bit counter is incremented on the tape once per real edge
occurrence; slots are not computed by an uncharged random-access index. -/
namespace J6R14LayoutCost
open AOracleMachineTime AOracleMachineTimeTape J6R12CollisionMenu

structure Seated where
  tag : Tagged
  address : SeatWords

def seatTraffic (kR kC b q a : ℕ) : ℕ :=
  4*(kR+kC+2*b+2*q+2*a+8)+12

def seatStepCap (kR kC b q a : ℕ) : ℕ :=
  12*q+(16*a+6)+seatTraffic kR kC b q a

def packRanks (kR kC b q a : ℕ) (m : AxisMarks) :
    List Bool → List Tagged → Meter (List Seated)
  | _,[] => ⟨[],0⟩
  | r,e::es =>
    let x := seatWords m r
    let v := addBits r (encodeBits q 1)
    let t := packRanks kR kC b q a m v.result es
    ⟨⟨e,x.result⟩::t.result,x.steps+v.steps+t.steps+seatTraffic kR kC b q a⟩

def ranksSpec (q : ℕ) (m : AxisMarks) : ℕ → List Tagged → List Seated
  | _,[] => []
  | j,e::es => ⟨e,(seatWords m (encodeBits q j)).result⟩::ranksSpec q m (j+1) es

theorem ranksSpec_at (q : ℕ) (m : AxisMarks) (j : ℕ) (es : List Tagged) (i : ℕ) :
    (ranksSpec q m j es)[i]?=es[i]?.map
      (fun e => ⟨e,(seatWords m (encodeBits q (j+i))).result⟩) := by
  induction es generalizing j i with
  | nil => simp [ranksSpec]
  | cons e es ih =>
    cases i with
    | zero => simp [ranksSpec]
    | succ i =>
      simpa [ranksSpec,Nat.succ_eq_add_one,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
        using (ih (j+1) i)

theorem ranksSpec_tags (q : ℕ) (m : AxisMarks) (j : ℕ) (es : List Tagged) :
    (ranksSpec q m j es).map Seated.tag=es := by
  induction es generalizing j with
  | nil => rfl
  | cons e es ih => simp [ranksSpec,ih]

theorem succWord (q j : ℕ) (hq : 0<q) (hj : j+1<2^q) :
    let s := addBits (encodeBits q j) (encodeBits q 1)
    s.result=encodeBits q (j+1) ∧ s.steps=12*q := by
  obtain ⟨hL,hv,hs⟩ := addBits_exact (encodeBits q j) (encodeBits q 1) (by rw [encodeBits_length,encodeBits_length])
  have hf : 1<(2:ℕ)^q := one_lt_pow₀ (by decide) hq.ne'
  have ht : j<2^q := by omega
  constructor
  · apply equal_width_inj
    · rw [hL,encodeBits_length,encodeBits_length]
    · rw [hv,encodeBits_exact _ _ ht,encodeBits_exact _ _ hf,encodeBits_length,
        Nat.mod_eq_of_lt hj,encodeBits_exact _ _ hj]
  · rwa [encodeBits_length] at hs

theorem packRanks_exact (kR kC b q a : ℕ) (hq : 0<q) (m : AxisMarks)
    (hm : m.length=a) (ha : a≤q) (j : ℕ) (es : List Tagged)
    (hf : j+es.length<2^q) :
    let t := packRanks kR kC b q a m (encodeBits q j) es
    t.result=ranksSpec q m j es ∧ t.steps≤es.length*seatStepCap kR kC b q a := by
  induction es generalizing j with
  | nil => simp [packRanks,ranksSpec]
  | cons e es ih =>
    have h' : j+1+es.length<2^q := by simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hf
    have hj : j+1<2^q := by omega
    obtain ⟨hn,hs⟩ := succWord q j hq hj
    obtain ⟨hp,hc⟩ := ih (j+1) h'
    have hx := (seatWords_exact m (encodeBits q j) (by rwa [hm,encodeBits_length])).2.2.2.2.2
    let x := seatWords m (encodeBits q j)
    let v := addBits (encodeBits q j) (encodeBits q 1)
    change x.steps=_ at hx
    rw [hm] at hx
    constructor
    · change Seated.mk e x.result::(packRanks kR kC b q a m v.result es).result=_
      rw [show v.result=_ from hn,hp]
      rfl
    · change x.steps+v.steps+(packRanks kR kC b q a m v.result es).steps+seatTraffic kR kC b q a≤_
      rw [show v.result=_ from hn,show v.steps=_ from hs,hx,List.length_cons,Nat.succ_mul es.length]
      unfold seatStepCap at hc ⊢
      omega

#print axioms ranksSpec_at
#print axioms ranksSpec_tags
#print axioms succWord
#print axioms packRanks_exact
end J6R14LayoutCost



