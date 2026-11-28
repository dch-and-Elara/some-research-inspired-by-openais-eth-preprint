
import J6R24LegalLayoutTokens
import J6R14LayoutCostRanks

/-! Fill actual address records with an incremented physical word; the
mate of each emitted word is the exact R14 header/selector/slot tape,
not a call to an uncharged address oracle. -/
namespace J6R24LegalLayout
open scoped BigOperators Classical
open J6R14LayoutCost P11FullPacking AOracleMachineTime AOracleMachineTimeTape
open J6R12CollisionEdges
set_option maxHeartbeats 12500000
set_option linter.unusedSectionVars false

structure AnchorWord where
  cell : CellWord
  rank : List Bool
  physical : RawAddress

def expectedAnchor (a q : ℕ) (k : CellWord) (j : ℕ) : AnchorWord :=
  let r := encodeBits q j
  ⟨k,r,(exportOne a k r).result⟩

def stepFee (a q : ℕ) := exportOneCap a+12*q+16*(a+q+1)+12

def seatRange (a q : ℕ) (k : CellWord) : List Bool→List Unit→Meter (List AnchorWord)
  | _,[] => ⟨[],4⟩
  | r,_::cs =>
    let p := exportOne a k r
    let inc := addBits r (encodeBits q 1)
    let u := seatRange a q k inc.result cs
    ⟨⟨k,r,p.result⟩::u.result,p.steps+inc.steps+u.steps+16*(a+q+1)+12⟩

theorem seat_range_exact (a b q : ℕ) (hq : 0<q) (ha : a≤q)
    (c : CellType a) (j : ℕ) (clock : List Unit)
    (h : j+clock.length≤b*2^a) (cap : b*2^a<2^q) :
    let out := seatRange a q (wordCell c) (encodeBits q j) clock
    out.result=List.ofFn (fun k : Fin clock.length=>expectedAnchor a q (wordCell c) (j+k.val)) ∧
      out.steps≤4+clock.length*stepFee a q := by
  induction clock generalizing j with
  | nil => simp [seatRange]
  | cons s cs ih =>
    let r := encodeBits q j
    let p := exportOne a (wordCell c) r
    let inc := addBits r (encodeBits q 1)
    have W : j+cs.length+1≤b*2^a := h
    have J : j+1<2^q := by omega
    have room : bitsValue r<b*2^a := by
      change bitsValue (encodeBits q j)<_
      rw [encodeBits_exact _ _ (by omega : j<2^q)]
      omega
    obtain ⟨hr,hc⟩ := succWord q j hq J
    obtain ⟨sr,sc⟩ := ih (j+1) (by omega : j+1+cs.length≤b*2^a)
    obtain ⟨_,_,_,_,_,pc⟩ := exportOne_exact c r (by simpa only [r,encodeBits_length] using ha) room
    constructor
    · change AnchorWord.mk (wordCell c) r p.result::
        (seatRange a q (wordCell c) inc.result cs).result=_
      rw [show inc.result=encodeBits q (j+1) from hr,sr,List.ofFn_succ]
      simp only [expectedAnchor,Fin.val_zero,Nat.add_zero]
      congr 1
      apply congrArg List.ofFn
      funext i
      have v : j+1+i.val=j+i.succ.val := by
        simp only [Fin.val_succ]
        omega
      rw [v]
    · change p.steps+inc.steps+(seatRange a q (wordCell c) inc.result cs).steps+16*(a+q+1)+12≤_
      rw [show inc.result=encodeBits q (j+1) from hr,show inc.steps=12*q from hc]
      simp only [List.length_cons,Nat.add_mul,one_mul]
      have zp : p.steps≤exportOneCap a := pc
      unfold stepFee at sc ⊢
      omega

def outRows (a q H : ℕ) (k : CellWord) : List AnchorWord :=
  List.ofFn (fun j : Fin H=>expectedAnchor a q k j.val)

def appendFee (a q : ℕ) := 32*(a+q+2)

def cellSeatFee (a q H : ℕ) :=
  4+H*stepFee a q+H*appendFee a q+6

def emitCells (a q H : ℕ) : List CellWord→Meter (List AnchorWord)
  | [] => ⟨[],5⟩
  | k::ks =>
    let p := seatRange a q k (encodeBits q 0) (List.replicate H ())
    let rest := emitCells a q H ks
    ⟨p.result++rest.result,p.steps+rest.steps+H*appendFee a q+6⟩

theorem emit_cells_exact (a b q : ℕ) (hq : 0<q) (ha : a≤q) (cap : b*2^a<2^q)
    (ks : List CellWord) (h : ∀ k∈ks,∃ c : CellType a,k=wordCell c) :
    let A := emitCells a q (b*2^a) ks
    A.result=ks.flatMap (outRows a q (b*2^a)) ∧
    A.steps≤5+ks.length*cellSeatFee a q (b*2^a) := by
  induction ks with
  | nil => simp [emitCells]
  | cons k ks ih =>
    obtain ⟨c,rfl⟩ := h k List.mem_cons_self
    have E := seat_range_exact a b q hq ha c 0 (List.replicate (b*2^a) ()) (by simp) cap
    simp only [List.length_replicate,Nat.zero_add] at E
    obtain ⟨eq,cost⟩ := ih (fun v hv=>h v (List.mem_cons_of_mem _ hv))
    constructor
    · simp only [emitCells,E.1,eq,List.flatMap_cons,outRows,Fin.coe_cast]
    · change (seatRange a q (wordCell c) (encodeBits q 0) (List.replicate (b*2^a) ())).steps+
        (emitCells a q (b*2^a) ks).steps+(b*2^a)*appendFee a q+6≤_
      rw [List.length_cons,Nat.add_mul,one_mul]
      have pe := E.2
      unfold cellSeatFee at cost ⊢
      omega

def allSeatWords (a b q : ℕ) : Meter (List AnchorWord) :=
  let keys := allPairsMachine (6*a)
  let full := emitCells a q (b*2^a) keys.result
  ⟨full.result,keys.steps+full.steps+6⟩

def completeSeatFee (a b q : ℕ) :=
  allPairsCap (6*a)+5+(2^(6*a)*2^(6*a))*cellSeatFee a q (b*2^a)+6

theorem all_seat_words_exact (a b q : ℕ) (hq : 0<q) (ha : a≤q) (cap : b*2^a<2^q) :
    (allSeatWords a b q).result=(allPairs (6*a)).flatMap (outRows a q (b*2^a)) ∧
      (allSeatWords a b q).steps≤completeSeatFee a b q := by
  obtain ⟨_,slots,_,len,fee⟩ := emitted_cells_exact a
  obtain ⟨keys,_⟩ := allPairsMachine_exact (6*a)
  have E := emit_cells_exact a b q hq ha cap (allPairsMachine (6*a)).result (fun k hk=>by
    obtain ⟨c,hc,_⟩ := slots k hk
    exact ⟨c,hc.symm⟩)
  constructor
  · change (emitCells a q (b*2^a) (allPairsMachine (6*a)).result).result=_
    rw [E.1,keys]
  · change (allPairsMachine (6*a)).steps+(emitCells a q (b*2^a) (allPairsMachine (6*a)).result).steps+6≤_
    have hc := E.2
    rw [len] at hc
    unfold completeSeatFee
    omega

#print axioms seat_range_exact
#print axioms emit_cells_exact
#print axioms all_seat_words_exact
end J6R24LegalLayout
