import J6R24MeteredRecursionFrame
import J6R12IntegralDirectPrinted

/-! R23's analytic certificates are discharged by the already established
R12 finite parent deformation of this same call. Supplying a raw execution
descriptor does not supply a polynomial, child reply, or origin answer. -/
namespace J6R24MeteredRecursion
open scoped Polynomial
open Polynomial J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable (r : Call (PhysicalHost f ell)) (hf : f.Monic) (he : 0<f.natDegree)
open scoped Classical in
noncomputable abbrev sourceDecision : DecidableEq (Envelope (N sel) (Childs sel) r) :=
  inferInstance

variable [env : DecidableEq (Envelope (N sel) (Childs sel) r)]

local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "Sh" => (paddedShape (N sel) (Childs sel) r)

noncomputable def sourceReplies (c : Call (PhysicalHost f ell)) : Responses Sh f ell c :=
  let B := J6R12Blueprint.sourceBlueprint sel r hf
  fun w=>B.program.run (B.program.child c w)

variable [Fact (Irreducible (NativeProbeRing.residuePoly f))] in
include cfg he in
set_option maxHeartbeats 5000000 in
theorem source_parent_sample (hr : Stable s C r) {c : Call (PhysicalHost f ell)}
    (hc : NativeReach (Plan sel) r c)
    (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
    (t : Center (paddedShape (N sel) (Childs sel) r) c) (z : Probe S c) :
    groupedSample Sh f ell c (sourceReplies sel r hf c) t z =
      ((J6R12Integral.actualJet sel d hf t.val).map (reduce (registerPrecision Sh c t) f ell)).eval
        (sampleNode Sh f ell c d.fit t z) := by
  have henv : env=sourceDecision sel r := Subsingleton.elim _ _
  subst env
  letI : DecidableEq (Envelope (N sel) (Childs sel) r) := sourceDecision sel r
  classical
  let B := J6R12Blueprint.sourceBlueprint sel r hf
  let G := J6R12Integral.printedGuards cfg sel r hr
  let D : B.SourceSpec := J6R12Integral.actualSourceSpec S (sourceDelta s) sel r G hf
  have hValid : D.Valid c := hc
  have repl : sourceReplies sel r hf c=(fun w=>B.expect (B.program.child c w)) := by
    funext w
    exact B.run_exact D hf he _ (D.child_valid c hValid d.active w)
  rw [repl]
  have e := D.grouped c hValid d.active t z
  have H : IsNative (N sel) (Childs sel) r c ∧ (S).cutoff<c.edges := ⟨hc,d.active⟩
  simpa only [D,J6R12Integral.actualSourceSpec,dif_pos H] using e


set_option maxHeartbeats 2500000 in
theorem source_active_value {c : Call (PhysicalHost f ell)}
    (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c) :
    (J6R12Blueprint.sourceBlueprint sel r hf).program.run c =
      assemble Sh f ell c d.fit (sourceReplies sel r hf c) := by
  let B := J6R12Blueprint.sourceBlueprint sel r hf
  have ha : (Sh).cutoff<c.edges := d.active
  change B.program.run c=_
  rw [Program.run,dif_neg (Nat.not_le.mpr ha)]
  change (if fit : ProofFit Sh f c then assemble Sh f ell c fit (sourceReplies sel r hf c) else 0)=_
  exact dif_pos d.fit

#print axioms source_parent_sample
#print axioms source_active_value
end J6R24MeteredRecursion



