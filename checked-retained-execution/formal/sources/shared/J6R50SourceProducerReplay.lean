import J6R49SourceLayoutHandoff
import J6R31RootResidentTablesRoster

/-! Replay an explicitly resident selected chart, without requiring it
to equal the stable greedy chart. The mask and geometry are the actual
bytes of that chart; no packed graph is fabricated from header-only
mode scratch. Only the source's complete mode roster is generated here. -/
namespace J6R50SourceProducer
open scoped Classical
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost
open J6R14LayoutCost J6R24LegalLayout J6R21Ancestor J6R27OriginalGate J6R31RootResidentTables P11FullPacking
open J6R32ChildResidentTransfer J6R48RawRoute J6R12CollisionEdges J6R17ModeTape
open J6R10Repack J6R9PacketScopes J6R33GeneratedChildSite
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8200000
set_option maxRecDepth 2500
set_option linter.unusedSectionVars false
set_option Elab.async false

def copyMaskRow {q : ℕ} (row : MaskRow q) : Meter (MaskRow q) :=
  let A := copyBytes row.address.labels.1
  let B := copyBytes row.address.labels.2
  let C := copyFixed row.address.copy
  let M := copyBytes row.bits
  ⟨⟨⟨(A.result,B.result),C.result⟩,M.result⟩,A.steps+B.steps+C.steps+M.steps+9⟩

def copiedMaskFee {q : ℕ} (x : MaskRow q) : ℕ :=
  3*(x.address.labels.1.length+x.address.labels.2.length+x.bits.length+q)+13

theorem copy_mask_row_exact {q : ℕ} (row : MaskRow q) :
    copyMaskRow row=⟨row,copiedMaskFee row⟩ := by
  rcases row with ⟨⟨⟨L,R⟩,c⟩,x⟩
  simp only [copyMaskRow,copyBytes_exact,copy_fixed_exact,copiedMaskFee]
  congr 1
  omega

def copyMaskTape {q : ℕ} : List (MaskRow q) → Meter (List (MaskRow q))
  | []=>⟨[],3⟩
  | x::xs=>
    let c := copyMaskRow x
    let t := copyMaskTape xs
    ⟨c.result::t.result,c.steps+t.steps+5⟩

theorem copy_mask_tape_exact {q : ℕ} (xs : List (MaskRow q)) :
    copyMaskTape xs=⟨xs,3+(xs.map (fun x=>copiedMaskFee x+5)).sum⟩ := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    simp only [copyMaskTape,copy_mask_row_exact,ih,List.map_cons,List.sum_cons]
    congr 1
    omega

def copySeatTape {a k : ℕ} : List (SeatField a k) → Meter (List (SeatField a k))
  | []=>⟨[],3⟩
  | x::xs=>
    let c := copySeat x
    let t := copySeatTape xs
    ⟨c.result::t.result,c.steps+t.steps+5⟩

theorem copy_seat_tape_exact {a k : ℕ} (xs : List (SeatField a k)) :
    copySeatTape xs=⟨xs,3+(3*(a+k)+51)*xs.length⟩ := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    simp only [copySeatTape,copied_seat_exact,ih,List.length_cons,Nat.mul_succ]
    congr 1
    omega

/-- Only the header scratch for enumerating mode identifiers is used
as packed metadata. A true R33 resident consumer reads the copies,
masks, seats and generated roster, never the scratch packed field. -/
def replaySelected (a q i : ℕ)
    (copies precision : Word (q+1)) (masks : List (MaskRow (q+1)))
    (seats : List (SeatField a ((q-a)+13*a))) : Meter (ChildResidents a q) :=
  let H := makeHeaders a
  let c := copyFixed copies
  let p := copyFixed precision
  let M := copyMaskTape masks
  let L := copySeatTape seats
  let R := buildTape (Nat.succ_pos q) a i 0 H.result c.result p.result
  ⟨⟨⟨⟨H.result,c.result.bits,[]⟩,c.result,M.result,R.result⟩,L.result⟩,
    H.steps+c.steps+p.steps+M.steps+L.steps+R.steps+10⟩

def selectedReplayFee (a q i copies p m n : ℕ) : ℕ :=
  headerBankFee a+2*(3*(q+1)+1)+(3+m)+(3+(3*(a+((q-a)+13*a))+51)*n)+
    buildCap a (q+1) (2^(6*a)*2^(6*a)) 0 0 copies (2^(i+1)) p+10

theorem paid_replay_of_any_selected_chart
    {E R C : Type} {N : Network E R C} {a q p : ℕ}
    (P : PhysicalPacking N a (Fin 64)) (i : Fin a) (ha : a≤q)
    (copies precision : Word (q+1)) (copyEq : copies.val=P.copies)
    (precisionEq : precision.val=p) (hp : 0<p) (hf : P.copies≤2^(q-a))
    (order : List E) (unique : order.Nodup) (all : ∀ e,e∈order) (edgeFit : order.length<2^q)
    (masks : List (MaskRow (q+1))) (hm : masks=(orderedChildPages a P.copies).map (encodeMaskRow P.mask))
    (seats : List (SeatField a ((q-a)+13*a)))
    (hs : seats=order.map (physicalSeatField P i (childPageKey (q-a)))) :
    let out := replaySelected a q i.val copies precision masks seats
    Nonempty (ResidentReceipt P i p out.result) ∧
      out.steps≤selectedReplayFee a q i.val P.copies p
        ((masks.map (fun x=>copiedMaskFee x+5)).sum) seats.length := by
  let H := makeHeaders a
  have hi : i.val+1<q+1 := by have h := i.isLt; omega
  obtain ⟨headers,size,n⟩ := actual_header_fields a
  obtain ⟨ms,hms,haM,modes,unq,weights,prec,fee⟩ :=
    buildTape_exact (Nat.succ_pos q) i hi 0 H.result (typedCells a)
      headers (typed_cells_exact a).1 (typed_cells_exact a).2.1
      copies precision copyEq precisionEq hp
  constructor
  · refine ⟨⟨order,unique,all,edgeFit,hf,?_,?_,?_,ms,hms,haM,?_,?_,?_,?_⟩⟩
    · unfold replaySelected
      rw [copy_fixed_exact]
      exact copyEq
    · unfold replaySelected
      change (copySeatTape seats).result=_
      rw [copy_seat_tape_exact]
      exact hs
    · unfold replaySelected
      change (copyMaskTape masks).result=_
      rw [copy_mask_tape_exact]
      exact hm
    all_goals
      unfold replaySelected
      rw [copy_fixed_exact,copy_fixed_exact]
      first | exact modes | exact unq | exact weights | exact prec
  · have hfee := (header_bank_exact a).2
    change H.steps≤_ at hfee
    change (buildTape (Nat.succ_pos q) a i.val 0 H.result copies precision).steps≤_ at fee
    change H.result.length=2^(6*a)*2^(6*a) at n
    change exportRows H.result=0 at size
    rw [n,size] at fee
    have pFee : (buildTape (Nat.succ_pos q) a i.val 0 H.result copies precision).steps≤
        buildCap a (q+1) (2^(6*a)*2^(6*a)) 0 0 P.copies (2^(i.val+1)) p := fee
    unfold replaySelected selectedReplayFee
    simp only [copy_fixed_exact,copy_mask_tape_exact,copy_seat_tape_exact]
    change H.steps+(3*(q+1)+1)+(3*(q+1)+1)+_+_+
      (buildTape (Nat.succ_pos q) a i.val 0 H.result copies precision).steps+10≤_
    omega

#print axioms copy_mask_row_exact
#print axioms copy_mask_tape_exact
#print axioms copy_seat_tape_exact
#print axioms paid_replay_of_any_selected_chart
end J6R50SourceProducer