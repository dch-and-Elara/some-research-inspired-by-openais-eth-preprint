
import J6R49DFSTypedVisit
import J6R50NonModeScratchStrip

/-! The selected strip fields are now attached to successful final
division of the very same streamed run at any active source path.
In particular a fallback word cannot impersonate a successful strip. -/
namespace J6R50Peak
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active J6R23ScheduleWeight
open J1PPrinted J6ActiveRun J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS J6R49DFS J6R50NonModeScratch

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 18000000

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

noncomputable abbrev liveHigh (R : StreamingResident T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (p : Path sel r c) (a : (S).cutoff<c.edges) :
    Block ((R.active p a).high (reachable_positive T p.reached)) ell :=
  ((R.active p a).highRun R.modeWidth (reachable_positive T p.reached) T.vPositive hf
    (actualChildRead R retire p a (stackBank R.births initial p))).result

noncomputable abbrev liveLow (R : StreamingResident T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (p : Path sel r c) : Block (T.frame p.reached) ell :=
  (nativeStream R retire c p (stackBank R.births initial p)).result.1

variable [DecidableEq (Envelope (N sel) (Childs sel) r)]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem same_run_active_strip_succeeds (R : StreamingResident T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (origin : R.rootLive initial)
    (legal : ReadyOnStack R.births initial) (p : Path sel r c) (a : (S).cutoff<c.edges) :
    let F := (R.active p a).high (reachable_positive T p.reached)
    let eq := (F.natDegree hf).trans ((T.frame p.reached).natDegree hf).symm
    (stripUVLoop eq (liveHigh R retire initial p a)).result=some (liveLow R retire initial p) := by
  let B := stackBank R.births initial p
  let d := ready_reachable cfg sel p.reached T.rootStable a
  let D := R.active p a
  let hp := reachable_positive T p.reached
  let read := actualChildRead R retire p a B
  have hChild (t : Center S c) (z : Probe S c) (β : NativeMenu (N sel) c t) (g : Fin 64) :
      (T.bank (registerPrecision S c t) (register_positive d t)).decode (read t z β g).result=
        (sourceBlueprint sel r hf).program.run ((Plan sel).child c ⟨⟨t,z,β,g⟩,d.active⟩) := by
    let w := addressed (sel:=sel) d t z β g
    have paid := (true_child_transaction R retire p a initial legal t z β g).1
    change (T.bank (registerPrecision S c t) (register_positive d t)).decode
      (actualChildRead R retire p a B t z β g).result=_
    rw [paid]
    exact stream_matches_printed R retire initial origin legal ((Plan sel).child c w) (.step p w)
  obtain ⟨x,old,_,_⟩ := actual_active_decoded cfg sel r hf p.reached d T.rootStable
    D.prior hp T.vPositive read hChild
  have finish : (D.finish R.modeWidth hp T.vPositive hf read).result=some x :=
    (active_finish_stream_value D R.modeWidth hp T.vPositive hf read).trans old
  have equality : liveLow R retire initial p=x := by
    unfold liveLow
    rw [active_phase_is_same_runner R retire p a]
    change (D.eval R.modeWidth hp T.vPositive hf read).result=x
    unfold ActiveMachine.eval checkedWord
    rw [finish]
  change (D.finish R.modeWidth hp T.vPositive hf read).result=some (liveLow R retire initial p)
  rw [finish,equality]

noncomputable def currentStripFields (R : StreamingResident T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (p : Path sel r c) (a : (S).cutoff<c.edges)
    (i : Fin ell) (j : Fin ((R.active p a).high (reachable_positive T p.reached)).words.length) :
    List Bool :=
  stripPauseFields (liveHigh R retire initial p a) (liveLow R retire initial p) i j

/-- The prefix bits come from the actual high sum and actual output
of the same scoped call; the next (i,j) strip position is real. -/
theorem same_run_strip_fields_cap (R : StreamingResident T key prec tw bw page q)
    (retire : J→ℕ) (initial : L) (origin : R.rootLive initial)
    (legal : ReadyOnStack R.births initial) (p : Path sel r c) (a : (S).cutoff<c.edges)
    (i : Fin ell) (j : Fin ((R.active p a).high (reachable_positive T p.reached)).words.length) :
    let Q := c.prec+(R.active p a).extraPrecision
    (currentStripFields R retire initial p a i j).length≤ell*(f.natDegree*Q)+
      ell*(f.natDegree*c.prec)+f.natDegree*c.prec+2*Q := by
  let H := (R.active p a).high (reachable_positive T p.reached)
  let he := (H.natDegree hf).trans ((T.frame p.reached).natDegree hf).symm
  have cap := (real_strip_pause he (liveHigh R retire initial p a) (liveLow R retire initial p)
    (same_run_active_strip_succeeds R retire initial origin legal p a) i j).2.2
  rw [H.natDegree hf] at cap
  exact cap

#print axioms same_run_active_strip_succeeds
#print axioms same_run_strip_fields_cap
end J6R50Peak
