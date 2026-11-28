
import J6R52PeakReader
import J6R50PeakLocal
import J6R50PeakAbsoluteCaps

/-! The completed high centre prefix and paused low jet are the
measured folds of the actual online callback. Nothing here identifies
online acquisition fees with those of the old prepared runner. -/
namespace J6R52Peak
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS J6R49DFS J6R50Peak J6R51Online

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 18500000
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "P" => (Plan sel)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

structure OnlineNumeric (M : OnlineMachine T key prec tw bw page q)
    (p : Path sel r c) (w : (P).Slot c) where
  before : List (Center S c)
  after : List (Center S c)
  split : (activeAt M p w.property).result.centres=before++(show Center S c from w.val.1)::after

theorem each_online_slot_has_the_native_numeric_pause
    (M : OnlineMachine T key prec tw bw page q) (p : Path sel r c) (w : (P).Slot c) :
    Nonempty (OnlineNumeric M p w) := by
  let D := (activeAt M p w.property).result
  let t : Center S c := w.val.1
  obtain ⟨pre,post,e⟩ := split_at_present t D.centres (D.centreComplete t)
  exact ⟨⟨pre,post,e⟩⟩

def OnlineNumeric.payload {M : OnlineMachine T key prec tw bw page q}
    {p : Path sel r c} {w : (P).Slot c} (Q : OnlineNumeric M p w)
    (retire : J→ℕ) (initial : L) : List Bool :=
  let D := (activeAt M p w.property).result
  pausedNumericFields D M.modeWidth (reachable_positive T p.reached) T.vPositive hf
    (readAt M retire initial p w.property) Q.before w.val.1 w.val.2.1

theorem resume_actual_online_numeric_prefix {M : OnlineMachine T key prec tw bw page q}
    {p : Path sel r c} {w : (P).Slot c} (Q : OnlineNumeric M p w)
    (retire : J→ℕ) (initial : L) :
    let prep := activeAt M p w.property
    let D := prep.result
    let hp := reachable_positive T p.reached
    let child := readAt M retire initial p w.property
    let out := D.eval M.modeWidth hp T.vPositive hf child
    let t := w.val.1
    let z := w.val.2.1
    runAt M retire initial p=⟨(out.result,stackBank (borns M) initial p),prep.steps+out.steps⟩ ∧
    D.highRun M.modeWidth hp T.vPositive hf child=
      resumeBlocks (D.high hp).hp (Q.before.map (centreRead D M.modeWidth hp T.vPositive hf child))
        (addM (D.high hp).hp
          (fromResumedJet D hp T.vPositive hf t (centrePause D M.modeWidth T.vPositive child t z).2)
          (sumM (D.high hp).hp (centreRead D M.modeWidth hp T.vPositive hf child) Q.after)) := by
  refine ⟨actual_online_active_phase M retire initial p w.property,?_⟩
  exact actual_active_resumes_from_nested_prefix (activeAt M p w.property).result M.modeWidth
    (reachable_positive T p.reached) T.vPositive hf (readAt M retire initial p w.property)
    Q.before Q.after w.val.1 w.val.2.1 Q.split

def ActualHighFit (M : OnlineMachine T key prec tw bw page q) (high : ℕ) : Prop :=
  ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (a : (S).cutoff<x.edges),
    x.prec+(activeAt M p a).result.extraPrecision≤high

def onlineNumericalCap (s C ell e low high : ℕ) : ℕ :=
  centreCap s*(ell*(e*high))+probeCap s*((4*(C*s))*(ell*(e*low)))

theorem actual_online_numeric_payload_cap {M : OnlineMachine T key prec tw bw page q}
    {p : Path sel r c} {w : (P).Slot c} (Q : OnlineNumeric M p w)
    (retire : J→ℕ) (initial : L) (high : ℕ) (fit : ActualHighFit M high) :
    (Q.payload retire initial).length≤onlineNumericalCap s C ell f.natDegree
      (absolutePrecision s r.edges r.prec) high := by
  let D := (activeAt M p w.property).result
  let d := ready_reachable cfg sel p.reached T.rootStable w.property
  let hpos := reachable_positive T p.reached
  let read := readAt M retire initial p w.property
  let t := w.val.1
  let z := w.val.2.1
  have hg : Q.before.length≤D.centres.length := by
    rw [Q.split,List.length_append,List.length_cons]
    omega
  have hlen := full_roster_length D.centres D.centreUnique D.centreComplete
  have hCt : Nat.card (Center S c)≤centreCap s :=
    (centers_le S c).trans (Nat.pow_le_pow_right (by decide)
      (Nat.succ_le_succ (bits_le_lam (Nat.clog 2 s) c.depth)))
  have hCenter := hg.trans (hlen.le.trans hCt)
  have theBound := d.fit
  change J9PrintedSchedule.probeCount c.edges (2^(S).levelBits c.depth)≤2^f.natDegree at theBound
  rw [cfg.coefficient] at theBound
  have hz := z.isLt
  change z.val<J9PrintedSchedule.probeCount c.edges (2^(S).levelBits c.depth) at hz
  have hProbe : z.val+2≤probeCap s := by unfold probeCap; omega
  obtain ⟨hu,huM⟩ := (J6R12Integral.printedGuards cfg sel r T.rootStable).taper _ p.reached w.property
  have ord := (order_bound c.edges ((S).levelWidth c.depth) t.val hu huM).trans
    (Nat.mul_le_mul_left 4 (actual_edges_uniform T p))
  have lo := absolute_register_precision_cap cfg sel T.rootStable p w.property t
  have hi := fit p w.property
  have raw := real_nested_payload_exact D M.modeWidth hpos T.vPositive hf read Q.before t z
  change (pausedNumericFields D M.modeWidth hpos T.vPositive hf read Q.before t z).length≤_
  rw [raw]
  exact Nat.add_le_add (Nat.mul_le_mul hCenter (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hi)))
    (Nat.mul_le_mul hProbe (Nat.mul_le_mul ord (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ lo))))

/-- A sufficient normal form for the same machine. This does not
replace its active producer or assert that it necessarily chose it. -/
def UsesPrintedCommon (M : OnlineMachine T key prec tw bw page q) : Prop :=
  ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (a : (S).cutoff<x.edges),
    (activeAt M p a).result.extraPrecision=
      commonLoss ((S).levelBits x.depth) x.edges ((S).levelWidth x.depth)

theorem printed_high_fit_without_replacing_runner (M : OnlineMachine T key prec tw bw page q)
    (printed : UsesPrintedCommon M) :
    ActualHighFit M (absoluteHighCap s C (absolutePrecision s r.edges r.prec)) := by
  intro x p a
  have hp := absolute_inherited_precision_cap cfg sel T.rootStable p
  have hm := actual_edges_uniform T p
  obtain ⟨hu,huM⟩ := (J6R12Integral.printedGuards cfg sel r T.rootStable).taper _ p.reached a
  have ha : (S).levelBits x.depth≤Nat.clog 2 s := bits_le_lam _ _
  have extra := simple_common_scale_cap ha hu huM
  rw [printed p a]
  exact Nat.add_le_add hp (extra.trans (Nat.mul_le_mul_right (commonSlope s) hm))

#print axioms each_online_slot_has_the_native_numeric_pause
#print axioms resume_actual_online_numeric_prefix
#print axioms actual_online_numeric_payload_cap
#print axioms printed_high_fit_without_replacing_runner
end
end J6R52Peak
