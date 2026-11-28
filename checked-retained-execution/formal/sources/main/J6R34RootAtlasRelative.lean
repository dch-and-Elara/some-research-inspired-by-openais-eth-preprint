import J6R34RootAtlasJoin
import J6R32StatefulArithmeticDepth
import J6R25PreparedSupplyRelative

/-! Charge each active occurrence relative to the actual exterior
call's absolute depth. No source precision or taper is reset to depth
zero when the original outer oracle asks for a generated child. -/
namespace J6R34RootAtlas
open scoped Polynomial BigOperators
open Polynomial AOracleMachineTime A1R10
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost J6R21Ancestor
open J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R25PreparedSupply J6R33StatefulArithmeticPage

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r)]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem reference_relative_depth (T : Prepared cfg sel r hf) :
    (reference T r (.reflexive r)).steps=
      ∑ j∈Finset.range (pathLimit s C+1),levelBill (Plan sel) r (activeArithmetic T) j := by
  have atRoot : referenceAt T r=(reference T r (.reflexive r)).steps := by
    unfold referenceAt
    rw [dif_pos (NativeReach.reflexive r)]
  rw [←atRoot]
  apply occurrence_tree_ledger (Plan sel) r (referenceAt T) (activeArithmetic T) (pathLimit s C)
  · intro j c hc
    exact reference_node_bill T (occurrence_reach_depth (Plan sel) (fun x=>x.depth) (fun _ _=>rfl) r j c hc).1
  · exact no_relative_terminal_children T

theorem joined_relative_ledger (actual : InputFamily T key prec tw bw page)
    (seed : PageJob f ell key prec tw bw page) (routes : RoutedInputs actual seed)
    (B : PageBank f ell key prec tw bw page)
    (ready : JobsReady B (seed::(pagedLog (compilerResident actual seed routes) r .root).jobs)) :
    let plan := compilerResident actual seed routes
    let log := Log.enter seed (pagedLog plan r .root)
    let out := startFromAtlas plan seed B
    (T.frame (.reflexive r)).decode out.result.1=reduce r.prec f ell (r.host.contract hf) ∧
      out.result.2=afterJobs B log.jobs ∧
      out.steps=(∑ j∈Finset.range (pathLimit s C+1),levelBill (Plan sel) r (activeArithmetic T) j)+
        chronologicalBill B log.jobs+log.extras B := by
  obtain ⟨word,state,fees⟩ := built_children_and_root_run actual seed routes B ready
  exact ⟨word,state,fees.trans (by rw [reference_relative_depth T])⟩

#print axioms reference_relative_depth
#print axioms joined_relative_ledger
end J6R34RootAtlas
