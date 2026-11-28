import J6R55CachedLedgerRoot
import J6R12IntegralDirectPrinted

/-! The same billed root word decodes to the literal physical network
contraction. Field degree positivity follows from the actual printed
guard, rather than becoming an additional premise. -/
namespace J6R55CachedLedger
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS J6R49DFS
open J6R50SourceProducer J6R26DescriptorTree J6R34ChildPath J6R49Cost J6R51
open J6R51Online J6R52CacheWhole J6R52Peak J6R53PeakAddon J6R54PeakInput

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3900
set_option maxHeartbeats 26000000
set_option linter.unusedSectionVars false
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem same_single_emission_exact_contraction_and_actual_occurrence_bill
    (M : OnlineMachine T key prec tw bw page q)
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (initial : PageBank f ell key prec tw bw page)
    (legal : ReadyOnStack (borns M) initial)
    (leaves : letI : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r) :=
      J6R24MeteredRecursion.sourceDecision sel r; LeafAgreement M initial)
    (rootFit : r.depth≤pathLimit s C) :
    let out := runCachedRootSingleEmission M retire initial
    (T.frame (Path.root : Path sel r r).reached).decode out.result.1=
        reduce r.prec f ell (r.host.contract hf) ∧ out.result.2=initial ∧
      out.steps ≤ ∑ j ∈ Finset.range (pathLimit s C-r.depth+1),
        levelBill (nativeScopedPlan sel r) ⟨r,Path.root⟩ (cachedOwn M retire initial) j := by
  have hClog : 0<Nat.clog 2 s :=
    lt_of_lt_of_le
      (Nat.mul_pos (pow_pos (show 0<2*epsDen by decide) 30) (pow_pos cfg.constPos 10))
      cfg.size
  have hF : 0<f.natDegree := by
    rw [cfg.coefficient]
    exact Nat.mul_pos (by decide) hClog
  letI : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r) :=
    J6R24MeteredRecursion.sourceDecision sel r
  obtain ⟨value,state,bill⟩ := same_single_emission_value_and_actual_occurrence_bill
    M retire initial legal leaves rootFit
  exact ⟨value.trans (J6R12Integral.printed_run_exact cfg sel r T.rootStable hf hF),state,bill⟩

#print axioms same_single_emission_exact_contraction_and_actual_occurrence_bill
end
end J6R55CachedLedger
