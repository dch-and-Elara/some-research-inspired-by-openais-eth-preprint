import J6R68OrdinalPeakMergePulse
import J6R53PeakAddonCore
import J6R49DFSReachEvents

/-! A paused pulse and the new live child belong to one and the same
successful ranked scope. Only these named fields are co-counted.
No result equality is used to transport peaks from the old runner. -/
namespace J6R68.OrdinalPeakMerge
open scoped Polynomial
open Polynomial AOracleMachineTime A1R12 J6R22Active J6R15ModeCost J6R16ModeCost J6R25PreparedSupply
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R21Ancestor J6R24MeteredRecursion J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R48RawRoute J6R49DFS
open J6R50SourceProducer J6R51Online J6R51ParentFrames J6R52Dispatch J6R52CacheWhole
open J6R54PeakInput J6R53PeakAddon J6R62ActivePrep J6R58OrdinalSpace J6R63Ordinal J6R63Active J6R64Active J6R66Active
open J6R66.BootPeak J6R68.RecursivePeak
set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 4550
set_option maxSynthPendingDepth 12
set_option maxHeartbeats 16300000
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw b : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {M : OnlineMachine T key prec tw bw page (q+1)}
variable {F : RetainedAfter T key prec tw bw page (q+1) cw}
variable {R : RankedRequests M F b} {x : Entered T key prec tw bw page}
variable {on : (printedParams (f:=f) (ell:=ell) s).cutoff<x.call.edges}
variable {t : Center (printedParams (f:=f) (ell:=ell) s) x.call}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "E" => (Entered T key prec tw bw page)
local notation "CF" => ((atActive M F x on).result.tape t).low

variable (H : PulseWitness R x on t) (cache : CachedParentFrames x.site.site)

def enteredAtRankedPulse (z : Probe SP x.call) (g : Fin 64) : E :=
  let w := atAddress x on t z H.mode g
  let next := (actualGroupLoad H cache z g).result.advance.next
  let child := afterOne x.bank next.birth.job
  ⟨x.call,nowPath x,w,next,(installResidentBank next).result,child,rfl⟩

theorem real_ranked_group_has_a_group_prefix (retire : J → ℕ) (recur : StateContinuation x)
    (z : Probe SP x.call) (g : Fin 64) :
    let one := oneM (CF).hp (CF).sizePos T.vPositive
    ∃ (remaining : List (Fin 64)) (inner : Block CF ell) (fee : ℕ),
      GroupPrefix (CF).hp (actualGroupCallback H cache retire recur z)
        one.result one.steps (g::remaining) inner fee :=
  every_left_group_is_visited _ _ _ _ g

theorem real_ranked_group_enters_the_same_child_and_tariff
    (retire : J → ℕ) (recur : StateContinuation x) (z : Probe SP x.call) (g : Fin 64)
    (legal : JobsReady x.bank [(enteredAtRankedPulse H cache z g).site.birth.job]) :
    let acq := actualGroupLoad H cache z g
    let child := enteredAtRankedPulse H cache z g
    let job := child.site.birth.job
    let run := recur child ((@Plan f ell s sel).smaller x.call child.slot)
    actualGroupCallback H cache retire recur z g=
      ⟨run.result.1,acq.steps+((produceCacheSidecarOnce acq.result cache).steps+
        (installResidentBank child.site).steps)+
        (publishFee x.bank job.entry job.offset job.built+run.steps+retire job+4)⟩ := by
  let w := atAddress x on t z H.mode g
  let acq := actualGroupLoad H cache z g
  let d := readyAtPath T (nowPath x) on
  let bad : Meter (Block CF ell) :=
    zeroM (T.bank (registerPrecision SP x.call t) (register_positive d t)).hp
  let go : (next : StoredSite T (successorTicket (x.path.ticket x.slot) w) key prec tw bw page) →
      WithIncoming next (Block CF ell) :=
    fun next res B own =>
     recur ⟨x.call,nowPath x,w,next,res,B,own⟩ ((@Plan f ell s sel).smaller x.call w)
  let child := enteredAtRankedPulse H cache z g
  let job := child.site.birth.job
  let run := recur child ((@Plan f ell s sel).smaller x.call child.slot)
  change project (openOnce acq cache retire go bad x.bank)=
    ⟨run.result.1,acq.steps+((produceCacheSidecarOnce acq.result cache).steps+
      (installResidentBank child.site).steps)+
      (publishFee x.bank job.entry job.offset job.built+run.steps+retire job+4)⟩
  rw [(open_once_enters_that_header_and_addon_bank acq cache retire go bad x.bank legal).1]; rfl

def selectedPauseAndChild (z : Probe SP x.call) (g : Fin 64) : ℕ :=
  let child := enteredAtRankedPulse H cache z g
  H.payload.length+mountedSelectedBits child.bank+
    (residentAddonPayload x.resident).length+(residentAddonPayload child.resident).length

theorem actual_pause_and_published_child_have_exact_selected_fields
    (z : Probe SP x.call) (g : Fin 64) :
    let child := enteredAtRankedPulse H cache z g
    ordinalObservedWords H.now H.index=some H.payload ∧
    selectedPauseAndChild H cache z g=
      (atTape M F x on t).words.length*(q+1)+2*b+
      mountedSelectedBits x.bank+mountedInsertionBits child.site.birth.job+
      (residentAddonPayload x.resident).length+(residentAddonPayload child.resident).length := by
  let child := enteredAtRankedPulse H cache z g
  have size := real_pulse_observation_is_same_row_and_two_words H
  refine ⟨size.1,?_⟩
  have bank : mountedSelectedBits child.bank =
      mountedSelectedBits x.bank+mountedInsertionBits child.site.birth.job :=
    publication_adds_exact_selected_record x.bank child.site.birth.job
  unfold selectedPauseAndChild
  dsimp only
  rw [size.2,bank]
  ac_rfl

#print axioms real_ranked_group_has_a_group_prefix
#print axioms real_ranked_group_enters_the_same_child_and_tariff
#print axioms actual_pause_and_published_child_have_exact_selected_fields
end
end J6R68.OrdinalPeakMerge

