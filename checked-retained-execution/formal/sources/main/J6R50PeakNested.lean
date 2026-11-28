
import J6R50PeakPrefix
import J6R49NonModeStackStreamed
import J6R49DFSActive

/-! The high centre prefix and the low interpolation prefix coexist
inside the same selected centre/probe of the actual streamed evaluator.
These are genuine results of the respective paid head-before-tail folds.
The observer is a proof-side payload/continuation, not a new runner. -/
namespace J6R50Peak
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active J6R23ScheduleWeight
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint
open J6R12Blueprint J6R24MeteredRecursion J1PPrinted J6R49DFS J6R49NonModeStack

set_option autoImplicit false
set_option maxHeartbeats 9500000
set_option maxRecDepth 3000

variable {f : ℤ[X]} {ell s q : ℕ}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {c : Call (PhysicalHost f ell)}
variable {d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c} {bank : Bank f}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

noncomputable abbrev centreRead (D : ActiveMachine sel d bank q)
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank) (t : Center S c) :
    Meter (Block (D.high hp) ell) :=
  (D.tape t).runCentre hq hv hf (D.high hp) D.extraPrecision (child t)

noncomputable abbrev centrePause (D : ActiveMachine sel d bank q)
    (hq : 0<q) (hv : 0<ell) (child : ActiveChild (sel:=sel) (d:=d) bank)
    (t : Center S c) (z : Probe S c) :
    List Bool × Meter (JetTape (D.tape t).low.words ell (D.tape t).window) :=
  let J := D.tape t
  observeStreamedCenter J.low J.tape.result hq hv
    (active_order_pos ((S).levelBits c.depth) c.edges ((S).levelWidth c.depth) t.val t.property)
    J.masks J.roster.rows (child t) z

noncomputable def pausedNumericFields (D : ActiveMachine sel d bank q)
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank)
    (before : List (Center S c)) (t : Center S c) (z : Probe S c) : List Bool :=
  completedBlockPayload (before.map (centreRead D hq hp hv hf child)) ++
    (centrePause D hq hv child t z).1

noncomputable def fromResumedJet (D : ActiveMachine sel d bank q)
    (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic) (t : Center S c)
    (w : Meter (JetTape (D.tape t).low.words ell (D.tape t).window)) :
    Meter (Block (D.high hp) ell) :=
  let J := D.tape t
  let out := sumM (D.high hp).hp
    (J.centreTerm hv hf (D.high hp) D.extraPrecision w.result) (List.range J.window)
  ⟨out.result,J.tape.steps+w.steps+out.steps+
    tapeFee J.low.words.length ell (registerPrecision S c t) J.window+4⟩

theorem actual_centre_uses_resumed_probe (D : ActiveMachine sel d bank q)
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank) (t : Center S c) (z : Probe S c) :
    centreRead D hq hp hv hf child t=fromResumedJet D hp hv hf t
      (centrePause D hq hv child t z).2 := by
  let J := D.tape t
  have h := (streamed_center_has_literal_suspended_jets hf J.low J.tape.result hq hv
    (active_order_pos ((S).levelBits c.depth) c.edges ((S).levelWidth c.depth) t.val t.property)
    J.masks J.roster.rows (child t) z).1
  have e : J.centreJet hq hv (child t)=(centrePause D hq hv child t z).2 := h
  change fromResumedJet D hp hv hf t (J.centreJet hq hv (child t))=_
  rw [e]

theorem actual_active_resumes_from_nested_prefix (D : ActiveMachine sel d bank q)
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank)
    (before after : List (Center S c)) (t : Center S c) (z : Probe S c)
    (split : D.centres=before++t::after) :
    D.highRun hq hp hv hf child=
      resumeBlocks (D.high hp).hp (before.map (centreRead D hq hp hv hf child))
        (addM (D.high hp).hp
          (fromResumedJet D hp hv hf t (centrePause D hq hv child t z).2)
          (sumM (D.high hp).hp (centreRead D hq hp hv hf child) after)) := by
  change sumM (D.high hp).hp (centreRead D hq hp hv hf child) D.centres=_
  rw [split]
  exact paid_sum_resumes_at (D.high hp).hp (centreRead D hq hp hv hf child) before t after _
    (actual_centre_uses_resumed_probe D hq hp hv hf child t z)

theorem real_nested_payload_exact (D : ActiveMachine sel d bank q)
    (hq : 0<q) (hp : 0<c.prec) (hv : 0<ell) (hf : f.Monic)
    (child : ActiveChild (sel:=sel) (d:=d) bank)
    (before : List (Center S c)) (t : Center S c) (z : Probe S c) :
    (pausedNumericFields D hq hp hv hf child before t z).length=
      before.length*(ell*(f.natDegree*(c.prec+D.extraPrecision)))+
        (z.val+2)*((D.tape t).window*(ell*(f.natDegree*registerPrecision S c t))) := by
  let J := D.tape t
  have h := (streamed_center_has_literal_suspended_jets hf J.low J.tape.result hq hv
    (active_order_pos ((S).levelBits c.depth) c.edges ((S).levelWidth c.depth) t.val t.property)
    J.masks J.roster.rows (child t) z).2.1
  rw [pausedNumericFields,List.length_append,completed_block_payload_exact,List.length_map,
    (D.high hp).natDegree hf]
  rw [show (centrePause D hq hv child t z).1.length =
    (z.val+2)*((D.tape t).window*(ell*(f.natDegree*registerPrecision S c t))) from h]

#print axioms actual_centre_uses_resumed_probe
#print axioms actual_active_resumes_from_nested_prefix
#print axioms real_nested_payload_exact
end J6R50Peak
