import J6R52PeakNumeric
import J6R53PeakAddonVisits
import J6R55CachedLedgerCore

/-! The current interpolation jet and completed high-centre values
are taken using the actual cached callback. The old uncached observer
is used only to transfer the width, which depends on dimensions and
index counts, not the decoded values returned by either callback. -/
namespace J6R57LiveSpace
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS J6R49DFS J6R50Peak J6R51Online J6R52Peak J6R53PeakAddon
open J6R52CacheWhole J6R55CachedLedger

set_option autoImplicit false
set_option maxRecDepth 3900
set_option maxHeartbeats 24500000
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (Plan sel)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

def cachedNumericPayload {M : OnlineMachine T key prec tw bw page q}
    {p : Path sel r c} {w : (P).Slot c} (Q : OnlineNumeric M p w)
    (retire : J→ℕ) (initial : L) : List Bool :=
  let D := (activeAt M p w.property).result
  pausedNumericFields D M.modeWidth (reachable_positive T p.reached) T.vPositive hf
    (cachedReadAt M retire initial p w.property) Q.before w.val.1 w.val.2.1

theorem actual_cache_visit_executes_the_observed_active_program
    (M : OnlineMachine T key prec tw bw page q) (retire : J→ℕ) (initial : L)
    (p : Path sel r c) (a : (S).cutoff<c.edges) :
    let A := activeAt M p a
    let got := A.result.eval M.modeWidth (reachable_positive T p.reached) T.vPositive hf
      (cachedReadAt M retire initial p a)
    cacheVisitAt M retire initial p=
      ⟨(got.result,stackBank (borns M) initial p),cacheMountFee M p+A.steps+got.steps⟩ := by
  cases p with
  | root =>
    simpa only [cacheVisitAt,cacheMountFee,activeAt,cachedReadAt,Nat.zero_add,stackBank] using
      actual_root_active_uses_the_exterior_child_reader M retire initial a
  | step prev u =>
    simpa only [cacheVisitAt,cacheMountFee,sourceBankAt,activeAt,cachedReadAt] using
      cached_active_phase_uses_the_selected_frame_cache M retire initial prev u a

theorem true_cached_numeric_pause_reenters_the_same_high_fold
    {M : OnlineMachine T key prec tw bw page q} {p : Path sel r c} {w : (P).Slot c}
    (Q : OnlineNumeric M p w) (retire : J→ℕ) (initial : L) :
    let D := (activeAt M p w.property).result
    let hp := reachable_positive T p.reached
    let child := cachedReadAt M retire initial p w.property
    let t := w.val.1
    let z := w.val.2.1
    D.highRun M.modeWidth hp T.vPositive hf child=
      resumeBlocks (D.high hp).hp (Q.before.map (centreRead D M.modeWidth hp T.vPositive hf child))
        (addM (D.high hp).hp
          (fromResumedJet D hp T.vPositive hf t (centrePause D M.modeWidth T.vPositive child t z).2)
          (sumM (D.high hp).hp (centreRead D M.modeWidth hp T.vPositive hf child) Q.after)) :=
  actual_active_resumes_from_nested_prefix (activeAt M p w.property).result M.modeWidth
    (reachable_positive T p.reached) T.vPositive hf (cachedReadAt M retire initial p w.property)
    Q.before Q.after w.val.1 w.val.2.1 Q.split

theorem actual_cache_numeric_payload_bound
    {M : OnlineMachine T key prec tw bw page q} {p : Path sel r c} {w : (P).Slot c}
    (Q : OnlineNumeric M p w) (retire : J→ℕ) (initial : L)
    (high : ℕ) (fit : ActualHighFit M high) :
    (cachedNumericPayload Q retire initial).length≤onlineNumericalCap s C ell f.natDegree
      (absolutePrecision s r.edges r.prec) high := by
  let D := (activeAt M p w.property).result
  let ready := reachable_positive T p.reached
  let eqA := real_nested_payload_exact D M.modeWidth ready T.vPositive hf
    (cachedReadAt M retire initial p w.property) Q.before w.val.1 w.val.2.1
  let eqB := real_nested_payload_exact D M.modeWidth ready T.vPositive hf
    (readAt M retire initial p w.property) Q.before w.val.1 w.val.2.1
  have width : (cachedNumericPayload Q retire initial).length=(Q.payload retire initial).length :=
    eqA.trans eqB.symm
  exact width.le.trans (actual_online_numeric_payload_cap Q retire initial high fit)

#print axioms actual_cache_visit_executes_the_observed_active_program
#print axioms true_cached_numeric_pause_reenters_the_same_high_fold
#print axioms actual_cache_numeric_payload_bound
end
end J6R57LiveSpace
