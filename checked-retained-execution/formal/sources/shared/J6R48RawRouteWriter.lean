import J6R36ChildFramedRouteCore
import J6R27OriginalGateSlots
import J6R27OriginalGateTrace
import J6R30GeneratedRootLayoutTags
import J6R25PreparedSupplyRegistry

/-! Create the *next* raw half-port rows using both actually framed
child lanes. Retape only the address and group of each lane, preserving
its body verbatim. All copies and appends below are finite bit loops. -/
namespace J6R48RawRoute
open scoped Classical
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R27OriginalGate J6R36ChildFramedRoute J6R30GeneratedRootLayout
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000
set_option Elab.async false

def oneBit (b : Bool) : Word 1 := ⟨[b],rfl⟩

def childHalfKey {w : ℕ} (old : Word w) (side : Bool) : Word (w+1) :=
  joinKey old (oneBit side)

theorem child_half_key_injective {w : ℕ} :
    Function.Injective (fun x : Word w×Bool=>childHalfKey x.1 x.2) := by
  intro u v e
  obtain ⟨addr,tag⟩ := join_key_equality e
  have same : u.2=v.2 := by
    have k := congrArg Word.bits tag
    change [u.2]=[v.2] at k
    exact List.cons.inj k |>.1
  exact Prod.ext addr same

def encodeHalf {w : ℕ} (old : Word w) (side : Bool) : Meter (Word (w+1)) :=
  let raw := appendBits old.bits [side]
  ⟨⟨raw.result,by
    change (appendBits old.bits [side]).result.length=w+1
    rw [append_bits_exact]
    simp [old.size]⟩,raw.steps+4⟩

theorem encoded_half_exact {w : ℕ} (old : Word w) (side : Bool) :
    encodeHalf old side=⟨childHalfKey old side,4*w+6⟩ := by
  change Meter.mk (Word.mk (appendBits old.bits [side]).result _)
    ((appendBits old.bits [side]).steps+4)=_
  apply congrArg₂ (fun (x : Word (w+1)) n=>Meter.mk x n)
  · apply word_bits_inj
    change (appendBits old.bits [side]).result=old.bits++[side]
    rw [append_bits_exact]
  · rw [append_bits_exact]
    simp only [old.size]
    omega

def nextPortView {w key prec page : ℕ} (b : Bool) (group : Word 6) (lane : Lane w key prec page) :
    PortRow (w+1) :=
  ⟨childHalfKey lane.id.edge b,group,lane.body⟩

def writeNextPort {w key prec page : ℕ} (b : Bool) (group : Word 6) (lane : Lane w key prec page) :
    Meter (PortRow (w+1)) :=
  let address := encodeHalf lane.id.edge b
  let grp := copyFixed group
  let bs := copyBytes lane.body
  ⟨⟨address.result,grp.result,bs.result⟩,address.steps+grp.steps+bs.steps+5⟩

def nextPortFee (w len : ℕ) := 4*w+3*len+31

theorem actual_next_port_exact {w key prec page : ℕ} (b : Bool) (group : Word 6)
    (lane : Lane w key prec page) :
    writeNextPort b group lane=⟨nextPortView b group lane,nextPortFee w lane.body.length⟩ := by
  simp only [writeNextPort,encoded_half_exact,copy_fixed_exact,copyBytes_exact,nextPortView,nextPortFee]
  congr 1
  omega

def rowsOfFrame {w owner key prec page a b : ℕ}
    (x : FramedEdge w owner key prec page) (seat : SeatField a b) : List (PortRow (w+1)) :=
  [nextPortView false seat.rowGroup x.left,nextPortView true seat.colGroup x.right]

def framedCopiesFee {w owner key prec page : ℕ} (x : FramedEdge w owner key prec page) : ℕ :=
  nextPortFee w x.left.body.length+nextPortFee w x.right.body.length

/-- One pass over the two aligned actual tapes, failing on a truncated
tape. There is no body reader at the next site apart from this writer. -/
def writeNextRows {w owner key prec page a b : ℕ} :
    List (FramedEdge w owner key prec page)→List (SeatField a b)→
      Meter (Option (List (PortRow (w+1))))
  | [],[]=>⟨some [],4⟩
  | [],_::_=>⟨none,4⟩
  | _::_,[]=>⟨none,4⟩
  | x::xs,s::ss=>
    let r := writeNextPort false s.rowGroup x.left
    let c := writeNextPort true s.colGroup x.right
    let rest := writeNextRows xs ss
    ⟨rest.result.map (fun rs=>r.result::c.result::rs),
      r.steps+c.steps+rest.steps+3*a+3*b+8⟩

theorem write_next_rows_exact {X : Type*} {w owner key prec page a b : ℕ}
    (order : List X) (frame : X→FramedEdge w owner key prec page) (seat : X→SeatField a b) :
    let run := writeNextRows (order.map frame) (order.map seat)
    run.result=some (order.flatMap (fun x=>rowsOfFrame (frame x) (seat x))) ∧
      run.steps=4+(order.map (fun x=>framedCopiesFee (frame x)+3*a+3*b+8)).sum := by
  induction order with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih =>
    obtain ⟨v,fee⟩ := ih
    simp only [List.map_cons,List.flatMap_cons,writeNextRows,actual_next_port_exact,v,fee,
      rowsOfFrame,List.cons_append,List.nil_append,Option.map_some,List.sum_cons,true_and,
      framedCopiesFee]
    omega

#print axioms child_half_key_injective
#print axioms encoded_half_exact
#print axioms actual_next_port_exact
#print axioms write_next_rows_exact
end J6R48RawRoute

