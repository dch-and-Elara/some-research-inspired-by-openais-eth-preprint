import J6R51OnlineVisitDefs

/-! Exact charges at the actual visited slot on the new threaded run.
This module is independent of the decoded-output induction and of
any uniform global envelope. -/
namespace J6R51Online
open scoped Polynomial
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R48RawRoute
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 3200
set_option maxHeartbeats 5500000
set_option maxSynthPendingDepth 12
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)
local notation "P" => (Plan sel)

theorem run_after_active_eq
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    {c : Call (PhysicalHost f ell)} (p : Path sel r c) (u : (@Plan f ell s sel).Slot c)
    (X : StoredSite T (p.ticket u) key prec tw bw page)
    (a : (printedParams (f:=f) (ell:=ell) s).cutoff<((@Plan f ell s sel).child c u).edges) (B : L) :
    runAfter M retire c p u X B=
      let A := M.activeAfter p u X a
      let out := A.result.eval M.modeWidth (reachable_positive T ((Path.step p u)).reached) T.vPositive hf
        (readAfter M retire p u X a B)
      (⟨(out.result,B),A.steps+out.steps⟩ : Meter (Block (T.frame ((Path.step p u)).reached) ell×L)) := by
  rw [runAfter,dif_neg (Nat.not_le.mpr a)]
  rfl

theorem run_root_active_eq
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (a : (printedParams (f:=f) (ell:=ell) s).cutoff<r.edges) (B : L) :
    runRoot M retire B=
      let D := M.activeRoot a
      let out := D.result.eval M.modeWidth (reachable_positive T (Path.root : Path sel r r).reached)
        T.vPositive hf (readRoot M retire a B)
      (⟨(out.result,B),D.steps+out.steps⟩ : Meter (Block (T.frame (Path.root : Path sel r r).reached) ell×L)) := by
  rw [runRoot,dif_neg (Nat.not_le.mpr a)]
  rfl

#print axioms run_after_active_eq
#print axioms run_root_active_eq
end
end J6R51Online
