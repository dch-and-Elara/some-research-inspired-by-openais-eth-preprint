
import J6R50PeakNested
import J6R49DFSTypedVisit

/-! A non-mode suspension at the very same typed Plan occurrence as a
mode emission. Its position is not selected by an independent cut.
The completed payload is computed from the real child-read function in
the parent bank, not from arbitrary hypothetical probe answers. -/
namespace J6R50Peak
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R48DFS J6R49DFS

set_option autoImplicit false
set_option maxRecDepth 3200
set_option maxHeartbeats 12000000

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

theorem split_at_present {A : Type*} (x : A) (order : List A) (member : x∈order) :
    ∃ before after, order=before++x::after := by
  induction order with
  | nil => simp at member
  | cons a tail ih =>
    rcases List.mem_cons.mp member with he | hm
    · subst a
      exact ⟨[],tail,rfl⟩
    · obtain ⟨l,r,split⟩ := ih hm
      exact ⟨a::l,r,congrArg (List.cons a) split⟩

structure NumericAt (R : StreamingResident T key prec tw bw page q)
    (p : Path sel r c) (w : (Plan sel).Slot c) where
  before : List (Center S c)
  after : List (Center S c)
  split : (R.active p w.property).centres=before++(show Center S c from w.val.1)::after

theorem actual_slot_has_numeric_pause (R : StreamingResident T key prec tw bw page q)
    (p : Path sel r c) (w : (Plan sel).Slot c) : Nonempty (NumericAt R p w) := by
  let D := R.active p w.property
  obtain ⟨before,after,e⟩ := split_at_present (show Center S c from w.val.1) D.centres (D.centreComplete w.val.1)
  exact ⟨⟨before,after,e⟩⟩

noncomputable def NumericAt.payload
    {R : StreamingResident T key prec tw bw page q} {p : Path sel r c} {w : (Plan sel).Slot c}
    (E : NumericAt R p w) (retire : J→ℕ) (initial : L) : List Bool :=
  let D := R.active p w.property
  let read := actualChildRead R retire p w.property (stackBank R.births initial p)
  pausedNumericFields D R.modeWidth (reachable_positive T p.reached) T.vPositive hf
    read E.before w.val.1 w.val.2.1

theorem actual_numeric_payload_at_address
    {R : StreamingResident T key prec tw bw page q} {p : Path sel r c} {w : (Plan sel).Slot c}
    (E : NumericAt R p w) (retire : J→ℕ) (initial : L) :
    let D := R.active p w.property
    let t := w.val.1
    let z := w.val.2.1
    (E.payload retire initial).length=
      E.before.length*(ell*(f.natDegree*(c.prec+D.extraPrecision)))+
        (z.val+2)*((D.tape t).window*(ell*(f.natDegree*registerPrecision S c t))) := by
  let D := R.active p w.property
  exact real_nested_payload_exact D R.modeWidth
    (reachable_positive T p.reached) T.vPositive hf
    (actualChildRead R retire p w.property (stackBank R.births initial p))
    E.before w.val.1 w.val.2.1

/-- The observed continuation resumes highRun of the same active
nativeStream. There is no change in evaluation, arithmetic, or fee. -/
theorem numeric_pause_is_in_same_runner
    {R : StreamingResident T key prec tw bw page q} {p : Path sel r c} {w : (Plan sel).Slot c}
    (E : NumericAt R p w) (retire : J→ℕ) (initial : L) :
    let D := R.active p w.property
    let B := stackBank R.births initial p
    let read := actualChildRead R retire p w.property B
    let hp := reachable_positive T p.reached
    let t := w.val.1
    let z := w.val.2.1
    nativeStream R retire c p B=
        (let out := D.eval R.modeWidth hp T.vPositive hf read
         (⟨(out.result,B),out.steps⟩ : Meter (Block (T.frame p.reached) ell × L))) ∧
      D.highRun R.modeWidth hp T.vPositive hf read=
        resumeBlocks (D.high hp).hp
          (E.before.map (centreRead D R.modeWidth hp T.vPositive hf read))
          (addM (D.high hp).hp
            (fromResumedJet D hp T.vPositive hf t (centrePause D R.modeWidth T.vPositive read t z).2)
            (sumM (D.high hp).hp (centreRead D R.modeWidth hp T.vPositive hf read) E.after)) := by
  exact ⟨active_phase_is_same_runner R retire p w.property _,
    actual_active_resumes_from_nested_prefix (R.active p w.property) R.modeWidth
      (reachable_positive T p.reached) T.vPositive hf
      (actualChildRead R retire p w.property (stackBank R.births initial p))
      E.before E.after w.val.1 w.val.2.1 E.split⟩

#print axioms actual_slot_has_numeric_pause
#print axioms actual_numeric_payload_at_address
#print axioms numeric_pause_is_in_same_runner
end J6R50Peak
