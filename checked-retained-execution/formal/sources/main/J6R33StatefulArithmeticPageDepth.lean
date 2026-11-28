import J6R33StatefulArithmeticPageWhole
import J6R32StatefulArithmeticDepth

namespace J6R33StatefulArithmeticPage
open scoped Polynomial BigOperators
open Polynomial AOracleMachineTime A1R10 J6ActiveRun J6R9Recursive J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost J6R21Ancestor
open J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r)]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem whole_paged_depth (R : PagedResident T key prec tw bw page) (d₀ : r.depth=0)
    (B : PageBank f ell key prec tw bw page) (ready : JobsReady B (pagedLog R r .root).jobs)
    (live : R.rootLive B) :
    let out := nativePaged R r .root B
    let log := pagedLog R r .root
    (T.frame (.reflexive r)).decode out.result.1=reduce r.prec f ell (r.host.contract hf) ∧
      out.result.2=afterJobs B log.jobs ∧
      out.steps=(∑ j∈Finset.range (pathLimit s C+1),levelBill (Plan sel) r (activeArithmetic T) j)+
        chronologicalBill B log.jobs+log.extras B := by
  obtain ⟨word,state,fee⟩ := whole_paged_subtree R r .root B ready live
  have enc := (whole_prepared_contraction T d₀).1
  have same := ((T.correctAt r (.reflexive r))).symm.trans enc
  exact ⟨word.trans same,state,fee.trans (by rw [reference_depth_sum T d₀])⟩

#print axioms whole_paged_depth
end J6R33StatefulArithmeticPage
