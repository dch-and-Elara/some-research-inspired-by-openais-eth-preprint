import J6R48RawRouteWriter
import J6R37StructuredRootCore

/-! Actual boot row assembly: copy the two R37 lane bodies into the first
native call's physical format. The new group words come from the actual
next selector's seat fields; the lane source is never an asserted body. -/
namespace J6R55BootBodies
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R37StructuredRoot J6R32RootGeneratedRegistryInputs J6R31RootResidentTables
open J6R48RawRoute J6R27OriginalGate J6R36ChildFramedRoute J6R26DescriptorTree
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2000
set_option maxHeartbeats 5500000
set_option Elab.async false

def bootPairRows {m key prec pad a b : ℕ} (lanes : RootLanes m key prec pad)
    (seat : SeatField a b) : List (PortRow (rootHalfWidth m+1)) :=
  [nextPortView false seat.rowGroup lanes.gate,nextPortView true seat.colGroup lanes.packet]

def bootPairFee {m key prec pad a b : ℕ} (lanes : RootLanes m key prec pad)
    (_ : SeatField a b) : ℕ :=
  nextPortFee (rootHalfWidth m) lanes.gate.body.length+
    nextPortFee (rootHalfWidth m) lanes.packet.body.length+3*a+3*b+8

/-- Same copying stage as the native writer, before any first-ticket
header is published. Reject length mismatches rather than inventing a
lane or reading hidden bytes from the proof's selected order. -/
def writeBootRows {m key prec pad a b : ℕ} :
    List (RootLanes m key prec pad)→List (SeatField a b)→
      Meter (Option (List (PortRow (rootHalfWidth m+1))))
  | [],[]=>⟨some [],4⟩
  | [],_::_=>⟨none,4⟩
  | _::_,[]=>⟨none,4⟩
  | x::xs,s::ss=>
    let r := writeNextPort false s.rowGroup x.gate
    let c := writeNextPort true s.colGroup x.packet
    let tail := writeBootRows xs ss
    ⟨tail.result.map (fun rs=>r.result::c.result::rs),
      r.steps+c.steps+tail.steps+3*a+3*b+8⟩

theorem written_boot_rows_exact {E : Type*} {m key prec pad a b : ℕ}
    (order : List E) (lanes : E→RootLanes m key prec pad) (seat : E→SeatField a b) :
    let run := writeBootRows (order.map lanes) (order.map seat)
    run.result=some (order.flatMap (fun x=>bootPairRows (lanes x) (seat x))) ∧
    run.steps=4+(order.map (fun x=>bootPairFee (lanes x) (seat x))).sum := by
  induction order with
  | nil=>exact ⟨rfl,rfl⟩
  | cons x xs ih=>
    obtain ⟨v,fee⟩ := ih
    simp only [List.map_cons,List.flatMap_cons,writeBootRows,actual_next_port_exact,v,fee,
      bootPairRows,List.cons_append,List.nil_append,Option.map_some,List.sum_cons,true_and,
      bootPairFee]
    omega

theorem original_lane_batch_exact {E A B : Type*} (f : A→Meter B) (src : E→A)
    (intended : E→B) (unit : ℕ) (order : List E)
    (read : ∀ e,f (src e)=⟨intended e,unit⟩) :
    J6R12CollisionEdges.mapMeter f (order.map src)=⟨order.map intended,(unit+6)*order.length⟩ := by
  induction order with
  | nil=>rfl
  | cons x xs ih=>
    simp only [List.map_cons,J6R12CollisionEdges.mapMeter,read,ih,List.length_cons,Nat.mul_succ]
    congr 1
    omega

#print axioms written_boot_rows_exact
#print axioms original_lane_batch_exact
end J6R55BootBodies
