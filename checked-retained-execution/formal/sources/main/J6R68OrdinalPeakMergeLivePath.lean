import J6R68OrdinalPeakMergeState
import J6R68OrdinalPeakMergePublication
import J6R68RecursivePeakVisit

/-! Anchor the switch at a real R68 live path, with the actual R66
child continuation (one switched active state, original continuation
below it). Equal returned outputs alone cannot transfer memory, so we
separately identify the exact published child and resident record. -/
namespace J6R68.OrdinalPeakMerge
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R22Active J6R15ModeCost J6R16ModeCost J6R25PreparedSupply
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R21Ancestor J6R24MeteredRecursion J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R48RawRoute J6R49DFS
open J6R50SourceProducer J6R51Online J6R51ParentFrames J6R52Dispatch J6R52CacheWhole
open J6R62ActivePrep J6R58OrdinalSpace J6R63Ordinal J6R63Active J6R64Active J6R66Active
open J6R68.RecursivePeak
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 4500
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 16000000
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew b : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {M : OnlineMachine T key prec tw bw page (q+1)}
variable {F : RetainedAfter T key prec tw bw page (q+1) cw}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)

theorem original_r68_live_parent_has_this_header_and_callback
    (E : RootInputs T key prec tw bw page cw ew) (retire : J → ℕ)
    (initial : L) (own : OwnsHeader E.header initial)
    (p : Path sel r c) (u : (@Plan f ell s sel).Slot c)
    (on : (SP).cutoff<((@Plan f ell s sel).child c u).edges) :
    let x := sourceEntered M initial p u
    atActive M F x on=liveActiveAt M F E initial own (.step p u) on ∧
    oldHeaderReader (M:=M) retire x (mountResident x.site x.resident).result on (fun y _=>runState M F retire y)=
      liveReaderAt M F retire initial (.step p u) on :=
  ⟨rfl,rfl⟩

theorem actual_r68_visit_has_this_one_current_rank_replacement
    (R : RankedRequests M F b) (wired : HasOldCheckedWiring R)
    (E : RootInputs T key prec tw bw page cw ew) (retire : J → ℕ)
    (initial : L) (own : OwnsHeader E.header initial)
    (p : Path sel r c) (u : (@Plan f ell s sel).Slot c) :
    let x := sourceEntered M initial p u
    (stateBodyWithCurrentRank R retire x (fun y _=>runState M F retire y)).result=
      (liveVisit M F E retire initial own (.step p u)).result := by
  let x := sourceEntered M initial p u
  exact (one_r66_state_can_switch_its_active_reader_without_changing_value R wired retire x
    (fun y _=>runState M F retire y)).trans
      (congrArg Meter.result (run_state_equation M F retire x).symm)

theorem actual_ranked_publication_installs_same_child_objects_on_the_r68_path
    (R : RankedRequests M F b) (wired : HasOldCheckedWiring R)
    (retire : J → ℕ) (initial : L)
    (p : Path sel r c) (u : (@Plan f ell s sel).Slot c)
    (on : (SP).cutoff<((@Plan f ell s sel).child c u).edges)
    (t : Center SP ((@Plan f ell s sel).child c u))
    (H : PulseWitness R (sourceEntered M initial p u) on t)
    (z : Probe SP ((@Plan f ell s sel).child c u)) (g : Fin 64)
    (ready : ReadyOnStack (borns M) initial) :
    let x := sourceEntered M initial p u
    let w := atAddress x on t z H.mode g
    let cache := (mountResident x.site x.resident).result
    let child := enteredAtRankedPulse H cache z g
    child=sourceEntered M initial (.step p u) w ∧ JobsReady x.bank [child.site.birth.job] := by
  let x := sourceEntered M initial p u
  let w := atAddress x on t z H.mode g
  let cache := (mountResident x.site x.resident).result
  let child := enteredAtRankedPulse H cache z g
  have same :
      (actualGroupLoad H cache z g).result=(M.demand x.site w).result :=
    (live_rank_load_and_old_scope_use_same_packet_and_return R wired retire x cache on
      (fun y _=>runState M F retire y) t z H.mode H.raw H.index H.data.1 H.data.2 g).1
  let assemble (data : LocalLoad x.site w) : Entered T key prec tw bw page :=
    let n := data.advance.next
    let bank := afterOne x.bank n.birth.job
    ⟨x.call,nowPath x,w,n,(installResidentBank n).result,bank,rfl⟩
  have fields : child=sourceEntered M initial (.step p u) w := by
    change assemble (actualGroupLoad H cache z g).result=assemble (M.demand x.site w).result
    exact congrArg assemble same
  refine ⟨fields,?_⟩
  change JobsReady x.bank [child.site.birth.job]
  rw [fields]
  exact ready (.step p u) w

#print axioms original_r68_live_parent_has_this_header_and_callback
#print axioms actual_r68_visit_has_this_one_current_rank_replacement
#print axioms actual_ranked_publication_installs_same_child_objects_on_the_r68_path
end
end J6R68.OrdinalPeakMerge

