import J6R68RecursivePeakScope
import J6R66ActiveLedger
import J6R53PeakAddonVisits

/-! Proof-side names for the very state and callbacks of the R66
well-founded interpreter, at an actual typed physical path. The
site and live directory are linked to the runtime open, not inferred
from an equal final contraction. -/
namespace J6R68.RecursivePeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R12 J6R22Active
open J6R63Active J6R62ActivePrep J6R64Active J6R66Active
open J6R51Online J6R51ParentFrames J6R52CacheWhole J6R48RawRoute
open J6ActiveSchedule J6R9Recursive J6R16ModeCost J6R21Ancestor J6R48DFS
open J6R10Repack J6R34ChildPath J6R54PeakInput J6R53PeakAddon J6R55CachedLedger J6R52Peak
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R50SourceProducer J6R26DescriptorTree J6R24MeteredRecursion J6R49DFS
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6R66.BootPeak
set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 16000000
set_option maxRecDepth 4450
set_option Elab.async false

noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams
variable {f : ℤ[X]} {ell s C key prec tw bw page q cw ew : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (@Plan f ell s sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "Machine" => (OnlineMachine T key prec tw bw page q)
local notation "Here" => (Path.root : Path sel r r)

def sourceEntered (M : Machine) (initial : L)
    (p : Path sel r c) (w : (P).Slot c) : Entered T key prec tw bw page :=
  let X := sourceState M p w
  ⟨c,p,w,X,(installResidentBank X).result,stackBank (borns M) initial (.step p w),rfl⟩

def liveReaderAt (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (retire : J→ℕ) (initial : L) :
    {x : Call (PhysicalHost f ell)} → (p : Path sel r x) → (a : (S).cutoff<x.edges) →
      ActiveChild (sel:=sel) (d:=readyAtPath T p a) T.bank
  | _, .root,a =>
    let d := readyAtPath T Here a
    fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      project (bootWithHeader (M.initial w) retire (J6R66Active.runAfter M F retire r Here w)
        (zeroM (T.bank (registerPrecision S r t) (register_positive d t)).hp) initial)
  | _, .step p u,a =>
    let X := sourceState M p u
    let here := Path.step p u
    let d := readyAtPath T here a
    let current := (P).child _ u
    let mounted := mountResident X (installResidentBank X).result
    let B := stackBank (borns M) initial here
    fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      project (openOnce (M.demand X w) mounted.result retire
        (fun next=>J6R66Active.runAfter M F retire current here w next)
        (zeroM (T.bank (registerPrecision S current t) (register_positive d t)).hp) B)

def liveVisit (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (retire : J→ℕ)
    (initial : L) (rootOwn : OwnsHeader E.header initial) :
    {x : Call (PhysicalHost f ell)} → (p : Path sel r x) →
      Meter (Block (T.frame p.reached) ell×L)
  | _, .root => J6R66Active.runRoot M F E retire initial rootOwn
  | _, .step p w => runState M F retire (sourceEntered M initial p w)

theorem real_live_visit_uses_the_same_active_observands
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (retire : J→ℕ)
    (initial : L) (rootOwn : OwnsHeader E.header initial)
    (p : Path sel r c) (a : (S).cutoff<c.edges) :
    let A := liveActiveAt M F E initial rootOwn p a
    let out := A.result.eval M.modeWidth (reachable_positive T p.reached) T.vPositive hf
      (liveReaderAt M F retire initial p a)
    liveVisit M F E retire initial rootOwn p=
      ⟨(out.result,stackBank (borns M) initial p),cacheMountFee M p+A.steps+out.steps⟩ := by
  cases p with
  | root =>
    simp only [liveVisit,J6R66Active.runRoot,dif_neg (Nat.not_le.mpr a),liveActiveAt,liveReaderAt,stackBank,
      cacheMountFee,Nat.zero_add]
  | step p w =>
    change J6R66Active.runAfter M F retire _ p w (sourceState M p w)
      (installResidentBank (sourceState M p w)).result (stackBank (borns M) initial (.step p w)) rfl=_
    exact active_after_receives_current_header M F retire p w (sourceState M p w)
      (installResidentBank (sourceState M p w)).result (stackBank (borns M) initial (.step p w)) rfl a

theorem every_r66_live_reader_is_the_exact_metered_scoped_callback
    (M : Machine) (F : RetainedAfter T key prec tw bw page q cw)
    (E : RootInputs T key prec tw bw page cw ew) (retire : J→ℕ)
    (initial : L) (rootOwn : OwnsHeader E.header initial)
    (p : Path sel r c) (a : (S).cutoff<c.edges) :
    liveReaderAt M F retire initial p a=cachedReadAt (shadow M F E initial rootOwn) retire initial p a := by
  let Q := shadow M F E initial rootOwn
  cases p with
  | root =>
    have original := single_emission_first_reader_has_the_original_cached_meter Q retire initial a
    change liveReaderAt M F retire initial Here a=exteriorCachedRead Q retire initial a
    rw [←original]
    funext t z β g
    let d := readyAtPath T Here a
    let w := addressed (sel:=sel) d t z β g
    let bad : Meter (Block (T.bank (registerPrecision S r t) (register_positive d t)) ell) :=
      zeroM (T.bank (registerPrecision S r t) (register_positive d t)).hp
    change project (bootWithHeader (M.initial w) retire (J6R66Active.runAfter M F retire r Here w) bad initial)=
      project (bootBankDemand (M.initial w) retire (runCachedAfterSingleEmission Q retire r Here w) bad initial)
    refine congrArg project (boot_header_same_full_meter _ _ _ _ _ _ ?_)
    intro next live B own
    exact descendant_exact_meter M F E initial rootOwn retire r Here w next live B own
  | step p u =>
    have sites := shadow_stored_sites_unchanged M F E initial rootOwn p u
    change liveReaderAt M F retire initial (.step p u) a=sourceCachedRead Q retire initial p u a
    funext t z β g
    let now := (P).child _ u
    let here := Path.step p u
    let d := readyAtPath T here a
    let w := addressed (sel:=sel) d t z β g
    let bad : Meter (Block (T.bank (registerPrecision S now t) (register_positive d t)) ell) :=
      zeroM (T.bank (registerPrecision S now t) (register_positive d t)).hp
    let X := sourceState M p u
    let B := stackBank (borns M) initial here
    let cache := (mountResident X (installResidentBank X).result).result
    have equalHere :
        sourceCachedRead Q retire initial p u a t z β g=
          project (openBankDemand (M.demand X w) cache retire
            (runCachedAfter Q retire now here w) bad B) := by
      unfold sourceCachedRead sourceMounted
      dsimp only
      change project (openBankDemand (M.demand (sourceState Q p u) w)
          (mountResident (sourceState Q p u) (installResidentBank (sourceState Q p u)).result).result retire
          (runCachedAfter Q retire now here w) bad (stackBank (borns Q) initial here))=_
      change sourceState Q p u=sourceState M p u at sites
      rw [sites,shadow_births_unchanged M F E initial rootOwn]
    rw [equalHere]
    change project (openOnce (M.demand X w) cache retire (J6R66Active.runAfter M F retire now here w) bad B)=_
    rw [←single_local_emission_is_exactly_the_original_scoped_meter]
    refine congrArg project (open_once_same_full_meter _ _ _ _ _ _ _ ?_)
    intro next res bank own
    exact (descendant_exact_meter M F E initial rootOwn retire now here w next res bank own).trans
      (congrFun (all_depth_single_emission_preserves_cached_result_and_cost Q retire now here w next res) bank)

#print axioms sourceEntered
#print axioms real_live_visit_uses_the_same_active_observands
#print axioms every_r66_live_reader_is_the_exact_metered_scoped_callback
end
end J6R68.RecursivePeak
