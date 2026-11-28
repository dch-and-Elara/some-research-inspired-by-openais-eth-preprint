import J6R75RawPeakFoldBound
import J6R49NonModeStackStreamed

/-! The current half-jet of a paused raw probe is bounded on the
very emitted row, masks, roster, and child callback of that ancestor.
Its observer is not a heap allocation or a second centre evaluation. -/
namespace J6R75RawPeak
open scoped Polynomial Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active J6R9Recursive
open J6R63Active J6R62ActivePrep J6R64Active J6R66Active
open J6R51Online J6R48DFS J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6ActiveRun J6ActiveSchedule J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R16ModeCost J6R24MeteredRecursion J6R49DFS J6R49LiveBits
open J6R68ActiveInputs.Sweep J6R68.HermiteWeightScratch J6R68.RecursivePeak
open J6R50NonModeScratch J6R50Peak J6R52Peak J6R57ScopeFee J6R49NonModeStack
open J6R72SameRunRawScope J6R68.RetireScratch J6R68ActiveInputs

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option quotPrecheck false
set_option maxRecDepth 4500
set_option maxHeartbeats 6200000
set_option maxSynthPendingDepth 12

noncomputable section
variable {f : ℤ[X]} {ell s C q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

def rawAncestorJetRoof (s C ell e low : ℕ) : ℕ :=
  probeCap s*((4*(C*s))*(ell*(e*low)))

def observedRawHalfJet
    (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
    {bank : Bank f} (D : Schedule sel d bank q)
    (hq : 0<q) (hv : 0<ell)
    (child : ActiveChild (sel:=sel) (d:=d) bank) (x : D.EmitRow) (i : Probe S c) :
    List Bool × Meter (JetTape (D.fetch x).low.words ell (D.fetch x).window) :=
  let J := D.fetch x
  observeStreamedCenter J.low J.tape.result hq hv
    (active_order_pos ((S).levelBits c.depth) c.edges ((S).levelWidth c.depth)
      (D.tag x).val (D.tag x).property) J.masks J.roster.rows (child (D.tag x)) i

theorem actual_emitted_row_has_the_same_suspended_jet_width
    (p : Path sel r c) (a : (S).cutoff<c.edges)
    (D : Schedule sel (readyAtPath T p a) T.bank q)
    (hq : 0<q) (hv : 0<ell)
    (child : ActiveChild (sel:=sel) (d:=readyAtPath T p a) T.bank)
    (x : D.EmitRow) (i : Probe S c) :
    let pause := observedRawHalfJet (readyAtPath T p a) D hq hv child x i
    (D.fetch x).centreJet hq hv (child (D.tag x))=pause.2 ∧
    pause.1.length=(i.val+2)*((D.fetch x).window*(ell*(f.natDegree*registerPrecision S c (D.tag x)))) ∧
    pause.1.length≤rawAncestorJetRoof s C ell f.natDegree (absolutePrecision s r.edges r.prec) := by
  let d := readyAtPath T p a
  let J := D.fetch x
  let t := D.tag x
  have obs := streamed_center_has_literal_suspended_jets hf J.low J.tape.result hq hv
    (active_order_pos ((S).levelBits c.depth) c.edges ((S).levelWidth c.depth) t.val t.property)
    J.masks J.roster.rows (child t) i
  change J.centreJet hq hv (child t)=(observedRawHalfJet d D hq hv child x i).2 ∧
    (observedRawHalfJet d D hq hv child x i).1.length=(i.val+2)*(J.window*(ell*(f.natDegree*registerPrecision S c t))) ∧ _
  refine ⟨obs.1,obs.2.1,?_⟩
  rw [show (observedRawHalfJet d D hq hv child x i).1.length=
    (i.val+2)*(J.window*(ell*(f.natDegree*registerPrecision S c t))) from obs.2.1]
  have fit := d.fit
  change J9PrintedSchedule.probeCount c.edges (2^(S).levelBits c.depth)≤2^f.natDegree at fit
  rw [cfg.coefficient] at fit
  have idx := i.isLt
  change i.val<J9PrintedSchedule.probeCount c.edges (2^(S).levelBits c.depth) at idx
  have n : i.val+2≤probeCap s := by unfold probeCap; omega
  obtain ⟨hu,span⟩ := (J6R12Integral.printedGuards cfg sel r T.rootStable).taper _ p.reached a
  have order := (order_bound c.edges ((S).levelWidth c.depth) t.val hu span).trans
    (Nat.mul_le_mul_left 4 (actual_edges_uniform T p))
  have low := absolute_register_precision_cap cfg sel T.rootStable p a t
  exact Nat.mul_le_mul n (Nat.mul_le_mul order (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ low)))

#print axioms actual_emitted_row_has_the_same_suspended_jet_width
end
end J6R75RawPeak
