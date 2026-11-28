import J6R50LeafPage
import J6R36ChildFramedRouteWires

/-! The raw incidence chart for an inherited leaf vertex need not be
supplied as a preselected list. Copy the actual selected physical frame
headers into a shared owner-keyed tape, then scan its same old-owner
records. This projection does not change the original creation tag. -/
namespace J6R50Leaf
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R36ChildFramedRoute J6R34ChildPath J6R27OriginalGate
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 12000000

def leftRecord {w own key prec page : ℕ} (v : FramedEdge w own key prec page) :
    ResidentPort own w := ⟨v.oldOwner,requestView v.left⟩

def copyLeftRecord {w own key prec page : ℕ} (v : FramedEdge w own key prec page) :
    Meter (ResidentPort own w) :=
  let k := copyFixed v.oldOwner
  let line := copyRequest v.left
  ⟨⟨k.result,line.result⟩,k.steps+line.steps+5⟩

def copyLeft {w own key prec page : ℕ} : List (FramedEdge w own key prec page) →
    Meter (List (ResidentPort own w))
  | [] => ⟨[],2⟩
  | v::vs =>
    let head := copyLeftRecord v
    let tail := copyLeft vs
    ⟨head.result::tail.result,head.steps+tail.steps+4⟩

def carryPortFee (w own body : ℕ) := 3*own+wireFee w body+10

theorem copy_left_record_exact {w own key prec page : ℕ} (v : FramedEdge w own key prec page) :
    copyLeftRecord v=⟨leftRecord v,3*own+wireFee w v.left.body.length+6⟩ := by
  simp only [copyLeftRecord,copy_fixed_exact,copy_request_exact,leftRecord]
  congr 1
  omega

theorem copy_left_exact {w own key prec page : ℕ} (frames : List (FramedEdge w own key prec page)) :
    copyLeft frames=⟨frames.map leftRecord,
      2+(frames.map (fun v=>carryPortFee w own v.left.body.length)).sum⟩ := by
  induction frames with
  | nil => rfl
  | cons v vs ih =>
    rw [copyLeft,copy_left_record_exact,ih]
    simp only [List.map_cons,List.sum_cons,carryPortFee]
    congr 1
    omega

theorem same_retained_ports_from_paid_chart {w own key prec page : ℕ} (target : Word own)
    (frames : List (FramedEdge w own key prec page)) :
    (collectIncoming target (copyLeft frames).result).result=(collectRetained target frames).result := by
  rw [copy_left_exact]
  induction frames with
  | nil => rfl
  | cons x xs ih =>
    cases h : (cmpAddr target x.oldOwner).result
    · simp only [List.map_cons,collectIncoming,collectRetained,leftRecord,h,Bool.false_eq_true,if_false]
      exact ih
    · simp only [List.map_cons,collectIncoming,collectRetained,leftRecord,h,if_true,
        copy_incoming_exact,copy_request_exact]
      exact congrArg (requestView x.left :: ·) ih

#print axioms copy_left_exact
#print axioms same_retained_ports_from_paid_chart
end J6R50Leaf
