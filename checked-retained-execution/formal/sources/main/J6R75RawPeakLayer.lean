import J6R75RawPeakPriorRows
import J6R68RecursivePeakRosters
import J6R68ActiveInputsSweepWidth

/-! One raw parent at an actually issued row. Two named source
equalities identify the raw table and the callback with the live
interpreter. The rest is a selected-field certificate at this one
transition, not a change to the runner or a whole-stack claim. -/
namespace J6R75RawPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6R63Active J6R62ActivePrep J6R64Active J6R66Active
open J6R51Online J6R51ParentFrames J6R52CacheWhole J6R48DFS
open J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6ActiveSchedule
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R9Recursive J6R16ModeCost J6R24MeteredRecursion J6R49DFS J6R49LiveBits
open J6R68ActiveInputs.Sweep J6R68.HermiteWeightScratch J6R68.RecursivePeak J6R68.RetireScratch
open J6R50NonModeScratch J6R50Peak J6R52Peak J6R57LiveSpace J6R57ScopeFee J6R72SameRunRawScope

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 3900
set_option maxHeartbeats 4500000
set_option maxSynthPendingDepth 12

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew width : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)

def selectedParentBits (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
    {bank : Bank f} (D : Schedule sel d bank q)
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank)
    (mode : NativeSuspension (C:=C) (sel:=sel) c) (pre : List D.EmitRow) : ℕ :=
  rawStockBits D.stock+
    (scalarTermsPayload (pre.map (emittedCentreMeter D hq hp hv hf child))).length+
    (mode.measure.bits+(storedModeWeights mode).length+suspendedRosterBits mode)

theorem actual_raw_layer_binds_source_prior_rows_and_live_group
    (M : OnlineMachine T key prec tw bw page q) (F : RetainedAfter T key prec tw bw page q cw)
    (chart : MountedChart T) (E : RootInputs T key prec tw bw page cw ew)
    (B : L) (own : OwnsHeader E.header B) (tails : SavedDirectoryTails width)
    (legal : ReadyOnStack (borns M) B) (fits : q≤uniformWidth s C)
    (p : Path sel r c) (a : (S).cutoff<c.edges)
    (D : Schedule sel (readyAtPath T p a) T.bank q)
    (child : ActiveChild (sel:=sel) (d:=readyAtPath T p a) T.bank)
    (issued : D=(rawScheduleAt M F chart E B own p a).result)
    (callback : child=rawReaderAt M F chart (retireSavedDirectory tails) B p a)
    (x : D.EmitRow) (z : Probe S c) (β : NativeMenu (N sel) c (D.tag x)) (g : Fin 64) :
    let hp := reachable_positive T p.reached
    let obs := observedRawReader M F chart tails B p a (D.tag x) z β g
    let run := emittedCentreMeter D M.modeWidth hp T.vPositive hf child
    D.stock=(rawScheduleAt M F chart E B own p a).result.stock ∧
    project obs.1=child (D.tag x) z β g ∧ obs.2=some ⟨tails,tails⟩ ∧
    obs.1.result.2=stackBank (borns M) B p ∧
    ∃ (mode : NativeSuspension (C:=C) (sel:=sel) c) (pre post : List D.EmitRow),
      SawEmittedProbe (readyAtPath T p a) D M.modeWidth T.vPositive child x z β g mode ∧
      actualEmittedCentreRows D=pre++x::post ∧
      D.highRun M.modeWidth hp T.vPositive hf child=resumeUV (D.high hp).hp (pre.map run)
        (addM (D.high hp).hp (run x) (sumM (D.high hp).hp run post)) ∧
      selectedParentBits (readyAtPath T p a) D M.modeWidth hp T.vPositive hf child mode pre=
        rawStockBits D.stock+pre.length*(ell*((D.high hp).words.length*(c.prec+D.extra)))+
        (mode.measure.bits+(storedModeWeights mode).length+suspendedRosterBits mode) := by
  let hp := reachable_positive T p.reached
  let obs := observedRawReader M F chart tails B p a (D.tag x) z β g
  obtain ⟨seen,words,state⟩ :=
    actual_raw_reader_returns_through_its_own_saved_tail_cut M F chart tails B legal p a (D.tag x) z β g
  have meter : project obs.1=child (D.tag x) z β g := by
    rw [callback]
    exact seen
  obtain ⟨mode,pre,post,probe,split,cut,width,_⟩ :=
    actual_raw_fold_and_current_group_have_one_earlier_output_prefix (readyAtPath T p a) D fits
      M.modeWidth hp T.vPositive hf child x z β g
  refine ⟨congrArg Schedule.stock issued,meter,words,state,mode,pre,post,probe,split,cut,?_⟩
  unfold selectedParentBits
  rw [width]

/-- Every address of the actual typed plan is named by a row of this
same issued stock; the dependent native menu is reindexed only by its
equal centre key. -/
theorem every_native_slot_is_addressed_by_a_literal_raw_row
    (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
    {bank : Bank f} (D : Schedule sel d bank q) (w : (@Plan f ell s sel).Slot c) :
    ∃ (x : D.EmitRow) (z : Probe S c) (β : NativeMenu (N sel) c (D.tag x)) (g : Fin 64),
      addressed (sel:=sel) d (D.tag x) z β g=w := by
  rcases w with ⟨⟨t,z,β,g⟩,on⟩
  obtain ⟨x,name⟩ := D.tag_surj t
  subst t
  exact ⟨x,z,β,g,Subtype.ext rfl⟩

#print axioms every_native_slot_is_addressed_by_a_literal_raw_row
#print axioms actual_raw_layer_binds_source_prior_rows_and_live_group
end
end J6R75RawPeak
