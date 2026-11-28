import J6R68ActiveInputsSweepRun
import J6R68RecursivePeakVisit
import J6R68RetireScratchR66

/-! Expose the retirement cut of the exact reader of an active raw-sweep call.
The boot and descendant routes use the same original input, continuation,
publish guard and bank as the raw runner. The additional result is an
observation, not an extra run or additional time charge. -/
namespace J6R72SameRunRawScope
open scoped Polynomial
open Polynomial AOracleMachineTime J6R21Ancestor J6R26DescriptorTree
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R50SourceProducer J6R24MeteredRecursion
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R51Online J6R51ParentFrames J6R52CacheSource J6R52CacheWhole J6R48RawRoute
open J6R54PeakInput J6R57ScopeFee J6R64Active J6R66Active J6R68.RecursivePeak J6R68.RetireScratch
open J6R68ActiveInputs.Sweep
open J6R48DFS J6R9Recursive J6R22Active J6R63Active J6R62ActivePrep J6R49DFS J6R55CachedLedger J6ActiveSchedule

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 18000000
set_option maxRecDepth 4700
set_option maxSynthPendingDepth 12

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {f : ℤ[X]} {ell s C key prec tw bw page width q cw : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "Here" => (Path.root : Path sel r r)

/-- Raw sweep callback itself: the same ingress as R66, but the
actual continuation is the raw runner, not the old active supplier. -/
def rawReaderAt (M : OnlineMachine T key prec tw bw page q)
    (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (retire : PageJob f ell key prec tw bw page→ℕ) (B : L) :
    {x : Call (PhysicalHost f ell)} → (p : Path sel r x) → (a : (S).cutoff<x.edges) →
      ActiveChild (sel:=sel) (d:=readyAtPath T p a) T.bank
  | _, .root,a =>
    let d := readyAtPath T Here a
    fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      project (bootWithHeader (M.initial w) retire (runRawAfter M F chart retire r Here w)
        (zeroM (T.bank (registerPrecision S r t) (register_positive d t)).hp) B)
  | _, .step p u,a =>
    let X := sourceState M p u
    let here := Path.step p u
    let d := readyAtPath T here a
    let current := (P).child _ u
    let mounted := mountResident X (installResidentBank X).result
    let parent := stackBank (borns M) B here
    fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      project (openOnce (M.demand X w) mounted.result retire
        (fun next=>runRawAfter M F chart retire current here w next)
        (zeroM (T.bank (registerPrecision S current t) (register_positive d t)).hp) parent)

def observedRawReader (M : OnlineMachine T key prec tw bw page q)
    (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (tails : SavedDirectoryTails width) (B : L) :
    {x : Call (PhysicalHost f ell)} → (p : Path sel r x) → (a : (S).cutoff<x.edges) →
    (t : Center S x) → Probe S x → NativeMenu (N sel) x t → Fin 64 →
    Meter (Block (T.bank (registerPrecision S x t)
      (register_positive (readyAtPath T p a) t)) ell × L) × Option (TailCopyObservation width)
  | _, .root,a,t,z,β,g =>
    let d := readyAtPath T Here a
    let w := addressed (sel:=sel) d t z β g
    observeBootWithHeader (M.initial w) tails
      (runRawAfter M F chart (retireSavedDirectory tails) r Here w)
      (zeroM (T.bank (registerPrecision S r t) (register_positive d t)).hp) B
  | _, .step p u,a,t,z,β,g =>
    let X := sourceState M p u
    let here := Path.step p u
    let d := readyAtPath T here a
    let current := (P).child _ u
    let mounted := mountResident X (installResidentBank X).result
    let parent := stackBank (borns M) B here
    let w := addressed (sel:=sel) d t z β g
    observeOpenOnce (M.demand X w) mounted.result tails
      (fun next=>runRawAfter M F chart (retireSavedDirectory tails) current here w next)
      (zeroM (T.bank (registerPrecision S current t) (register_positive d t)).hp) parent

theorem raw_observer_projects_exactly_to_its_own_callback
    (M : OnlineMachine T key prec tw bw page q)
    (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (tails : SavedDirectoryTails width) (B : L) (p : Path sel r c) (a : (S).cutoff<c.edges) :
    (fun t z β g=>project (observedRawReader M F chart tails B p a t z β g).1)=
      rawReaderAt M F chart (retireSavedDirectory tails) B p a := by
  funext t z β g
  cases p with
  | root =>
    exact congrArg project (observed_boot_preserves_the_actual_meter _ _ _ _ _)
  | step p u =>
    exact congrArg project (observed_open_once_preserves_the_actual_meter _ _ _ _ _ _)

/-- The full active callback Meter projects unchanged. For a legal
publication the exact source/copy tails are observed, and the enclosing
scope returns the original parent bank, not the child's bank. -/
theorem actual_raw_reader_returns_through_its_own_saved_tail_cut
    (M : OnlineMachine T key prec tw bw page q)
    (F : RetainedAfter T key prec tw bw page q cw) (chart : MountedChart T)
    (tails : SavedDirectoryTails width) (B : L) (ready : ReadyOnStack (borns M) B)
    (p : Path sel r c) (a : (S).cutoff<c.edges)
    (t : Center S c) (z : Probe S c) (β : NativeMenu (N sel) c t) (g : Fin 64) :
    let obs := observedRawReader M F chart tails B p a t z β g
    project obs.1=rawReaderAt M F chart (retireSavedDirectory tails) B p a t z β g ∧
      obs.2=some ⟨tails,tails⟩ ∧ obs.1.result.2=stackBank (borns M) B p := by
  cases p with
  | root =>
    let d := readyAtPath T Here a
    let w := addressed (sel:=sel) d t z β g
    let go := runRawAfter M F chart (retireSavedDirectory tails) r Here w
    let bad : Meter (Block (T.bank (registerPrecision S r t) (register_positive d t)) ell) :=
      zeroM (T.bank (registerPrecision S r t) (register_positive d t)).hp
    have legal : JobsReady B [(M.initial w).result.birth.job] := ready Here w
    rw [show observedRawReader M F chart tails B Here a t z β g=
      observeBootWithHeader (M.initial w) tails go bad B from rfl]
    rw [observed_boot_on_the_actual_first_slot_has_two_tail_copies (M.initial w) tails go bad B legal]
    refine ⟨rfl,rfl,?_⟩
    exact congrArg (fun meter=>meter.result.2)
      (boot_header_enters_that_first_bank (M.initial w) (retireSavedDirectory tails) go bad B legal).1
  | step p u =>
    let X := sourceState M p u
    let here := Path.step p u
    let d := readyAtPath T here a
    let now := (P).child _ u
    let parent := stackBank (borns M) B here
    let w := addressed (sel:=sel) d t z β g
    let cache := (mountResident X (installResidentBank X).result).result
    let go := runRawAfter M F chart (retireSavedDirectory tails) now here w
    let bad : Meter (Block (T.bank (registerPrecision S now t) (register_positive d t)) ell) :=
      zeroM (T.bank (registerPrecision S now t) (register_positive d t)).hp
    have legal : JobsReady parent [(M.demand X w).result.advance.next.birth.job] := ready here w
    rw [show observedRawReader M F chart tails B here a t z β g=
      observeOpenOnce (M.demand X w) cache tails go bad parent from rfl]
    rw [observed_open_once_on_the_actual_successor_has_two_tail_copies (M.demand X w) cache tails go bad parent legal]
    refine ⟨rfl,rfl,?_⟩
    exact congrArg (fun meter=>meter.result.2)
      (open_once_enters_that_header_and_addon_bank (M.demand X w) cache
       (retireSavedDirectory tails) go bad parent legal).1

#print axioms observedRawReader
#print axioms raw_observer_projects_exactly_to_its_own_callback
#print axioms actual_raw_reader_returns_through_its_own_saved_tail_cut
end
end J6R72SameRunRawScope
