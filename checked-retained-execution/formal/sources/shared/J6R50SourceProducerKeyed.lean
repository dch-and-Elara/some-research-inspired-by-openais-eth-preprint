import J6R50SourceProducerReplay
import J6R49SourceLayoutExport

/-! The stable edge identity is copied from the actual predecessor
frame, not generated as a new row number. Use that identity to read
the chosen chart by sequential keyed lookup in native edge order. -/
namespace J6R50SourceProducer
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R27OriginalGate
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun P11FullPacking J6R9PacketScopes J6R11Repack
open J6R32ChildResidentTransfer J6R48RawRoute J6R33GeneratedChildSite J6R49SourceLayout
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3000
set_option maxHeartbeats 8800000
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

def frameRecordKey {w owner key prec page : ℕ}
    (x : FramedEdge w owner key prec page) : Word w := x.left.id.edge

def frameKeys {w owner key prec page : ℕ} :
    List (FramedEdge w owner key prec page)→Meter (List (Word w))
  | []=>⟨[],3⟩
  | x::xs=>
    let key := copyFixed x.left.id.edge
    let traverse := readFramedIncidence x
    let rest := frameKeys xs
    ⟨key.result::rest.result,key.steps+traverse.steps+rest.steps+4⟩

theorem frame_keys_exact {w owner key prec page : ℕ}
    (rows : List (FramedEdge w owner key prec page)) :
    frameKeys rows=⟨rows.map frameRecordKey,3+(rows.map (fun x=>3*w+5+framedIncidenceFee x)).sum⟩ := by
  induction rows with
  | nil=>rfl
  | cons x xs ih=>
    simp only [frameKeys,copy_fixed_exact,framed_incidence_row_exact,ih,List.map_cons,List.sum_cons]
    congr 1
    omega

def replayWithKeys {w owner key prec page : ℕ}
    (a q i : ℕ) (copies precision : Word (q+1)) (masks : List (MaskRow (q+1)))
    (bank : List (RefRow w (SeatField a ((q-a)+13*a))))
    (frames : Option (List (FramedEdge w owner key prec page))) :
    Meter (Option (ChildResidents a q)) :=
  match frames with
  | none=>⟨none,3⟩
  | some xs =>
    let keys := frameKeys xs
    let seats := restoreSeats bank keys.result
    match seats.result with
    | none => ⟨none,keys.steps+seats.steps+4⟩
    | some rows =>
      let found := replaySelected a q i copies precision masks rows
      ⟨some found.result,keys.steps+seats.steps+found.steps+7⟩

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {Q : Birth T v key prec tw bw page}
variable {previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
variable (S : SiteInputs Q previous)
variable (u : (Plan sel).Slot v.child) (q : ℕ)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) v.child.depth)
local notation "E" => v.child.host.Edge
local notation "d" => (ticketReady T (successorTicket v u))
local notation "t" => (Ticket.centerAt (successorTicket v u))
local notation "i" => (centerIndex d t)
local notation "p" => (registerPrecision SP v.child t)
local notation "P" => (packing sel d)
local notation "K" => ((q-A)+13*A)
local notation "edKey" => (childKey T v Q.native.physical)

structure ExplicitSelectedWords where
  copy : Word (q+1)
  copyExact : copy.val=(P).copies
  precision : Word (q+1)
  precisionExact : precision.val=p
  widthFit : A≤q
  edgesFit : (childOrder S).length<2^q
  copyFit : (P).copies≤2^(q-A)
  masks : List (MaskRow (q+1))
  masksExact : masks=(orderedChildPages A (P).copies).map (encodeMaskRow (P).mask)
  edges : List E
  all : ∀ x,x∈edges
  rows : List (RefRow Q.port (SeatField A K))
  edgesExact : rows=edges.map (fun e=>⟨edKey e,physicalSeatField P i (childPageKey (q-A)) e⟩)

def replayChild (U : ExplicitSelectedWords S u q) : Meter (Option (ChildResidents A q)) :=
  replayWithKeys A q (i).val U.copy U.precision U.masks U.rows S.write.result.framed

structure Replayed (U : ExplicitSelectedWords S u q) where
  resident : ChildResidents A q
  output : (replayChild S u q U).result=some resident
  certificate : ResidentReceipt P i p resident
  orderEq : certificate.edges=childOrder S

theorem replay_actual_selected_from_parent_frames (U : ExplicitSelectedWords S u q) :
    ∃ _ : Replayed S u q U,
      (replayChild S u q U).steps≤
        (3+(((childOrder S).map (frameOf S)).map (fun x=>3*Q.port+5+framedIncidenceFee x)).sum)+
        (4+(childOrder S).length*(locateFee Q.port U.rows.length+3*(A+K)+54))+
        selectedReplayFee A q (i).val (P).copies p
          ((U.masks.map (fun x=>copiedMaskFee x+5)).sum) (childOrder S).length+7 := by
  let order := childOrder S
  let fms := order.map (frameOf S)
  let key := edKey
  let st := physicalSeatField P i (childPageKey (q-A))
  let raw := order.map st
  let Z := replaySelected A q (i).val U.copy U.precision U.masks raw
  obtain ⟨cert,bill⟩ := paid_replay_of_any_selected_chart P i U.widthFit U.copy U.precision U.copyExact
    U.precisionExact (register_positive d t) U.copyFit order (child_order_complete S).1
    (child_order_complete S).2 U.edgesFit U.masks U.masksExact raw rfl
  let K0 := frameKeys fms
  have Kt := frame_keys_exact fms
  have keyEq : K0.result=order.map key := by
    unfold K0
    rw [Kt]
    change fms.map frameRecordKey=_
    unfold fms
    rw [List.map_map]
    rfl
  have Kbill : K0.steps=3+(fms.map (fun x=>3*Q.port+5+framedIncidenceFee x)).sum :=
    congrArg Meter.steps Kt
  let Seat := restoreSeats U.rows K0.result
  have restored := restore_order_exact order U.edges key st (child_key_injective T v Q.native.physical)
    (fun e _=>U.all e)
  have got : Seat.result=some raw := by
    unfold Seat
    rw [U.edgesExact,keyEq]
    exact restored.1
  have sb : Seat.steps≤4+order.length*(locateFee Q.port U.rows.length+3*(A+K)+54) := by
    unfold Seat
    rw [U.edgesExact,keyEq,List.length_map]
    exact restored.2
  have runEq : replayChild S u q U = ⟨some Z.result,K0.steps+Seat.steps+Z.steps+7⟩ := by
    unfold replayChild replayWithKeys
    rw [source_framed_in_child_order S]
    dsimp only
    rw [show (restoreSeats U.rows (frameKeys ((childOrder S).map (frameOf S))).result).result=
      some raw from got]
  obtain ⟨H⟩ := cert
  -- The verification certificate records the exact input edge order.
  have ss : Z.result.seats=order.map st := by
    change (copySeatTape raw).result=_
    rw [copy_seat_tape_exact]
  let H' : ResidentReceipt P i p Z.result :=
    ⟨order,(child_order_complete S).1,(child_order_complete S).2,U.edgesFit,H.copiesFit,
      H.copyValue,ss,H.masks,H.modes,H.modesUnique,H.modesAll,H.rawModes,H.rawUnique,H.weights,H.prec⟩
  refine ⟨⟨Z.result,congrArg Meter.result runEq,H',rfl⟩,?_⟩
  rw [runEq]
  change K0.steps+Seat.steps+Z.steps+7≤_
  rw [Kbill]
  have eq : raw.length=order.length := List.length_map ..
  change Z.steps≤_ at bill
  rw [eq] at bill
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add_left sb _) bill) 7

#print axioms frame_keys_exact
#print axioms replay_actual_selected_from_parent_frames
end
end J6R50SourceProducer