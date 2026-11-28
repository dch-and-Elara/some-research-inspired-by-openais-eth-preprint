import J6R24MeteredRecursionWhole

/-! When the source suffix starts at a nonzero absolute depth, do not
reset the printed precision or taper. The same R24 prepared interpreter
has its own exact occurrence ledger over the relative levels of that
suffix. No mode-production cost is implied for such selectable roots. -/
namespace J6R25PreparedSupply
open scoped Polynomial BigOperators
open Polynomial AOracleMachineTime
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint
open J1PPrinted J6R16ModeCost J6R24MeteredRecursion

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf)

include T in
theorem no_relative_terminal_children :
    occurrences (Plan sel) r (pathLimit s C+1)=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  rw [occurrences,List.mem_flatMap] at hx
  obtain ⟨c,hc,hx⟩ := hx
  obtain ⟨w,_,_⟩ := List.mem_map.mp hx
  have eq := occurrence_reach_depth (Plan sel) (fun c=>c.depth) (fun _ _=>rfl) r (pathLimit s C) c hc
  have bad := active_strictly_before_limit cfg sel T.rootStable eq.1 w.property
  have ec : c.depth=r.depth+pathLimit s C := eq.2
  omega

theorem relative_prepared_bill :
    (T.run r (.reflexive _)).steps=
      ∑ j∈Finset.range (pathLimit s C+1),levelBill (Plan sel) r T.localAt j := by
  have atRoot : T.totalAt r=(T.run r (.reflexive _)).steps := by
    unfold Prepared.totalAt
    rw [dif_pos (NativeReach.reflexive r)]
  rw [←atRoot]
  apply occurrence_tree_ledger (Plan sel) r T.totalAt T.localAt (pathLimit s C)
  · intro j c hc
    exact T.node_bill (occurrence_reach_depth (Plan sel) (fun x=>x.depth) (fun _ _=>rfl) r j c hc).1
  · exact no_relative_terminal_children T

variable [env : DecidableEq (Envelope (N sel) (Childs sel) r)]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

set_option maxHeartbeats 3000000 in
theorem relative_prepared_contraction :
    let R := T.run r (.reflexive _)
    (T.frame (.reflexive _)).decode R.result=reduce r.prec f ell (r.host.contract hf) ∧
    R.steps=∑ j∈Finset.range (pathLimit s C+1),levelBill (Plan sel) r T.localAt j := by
  have eq : env=sourceDecision sel r := Subsingleton.elim _ _
  subst env
  letI : DecidableEq (Envelope (N sel) (Childs sel) r) := sourceDecision sel r
  let G := T.frame (NativeReach.reflexive r)
  have he : 0<f.natDegree := G.natDegree hf ▸ G.sizePos
  exact ⟨(T.correctAt r (.reflexive _)).trans
    (J6R12Integral.printed_run_exact cfg sel r T.rootStable hf he),relative_prepared_bill T⟩

#print axioms no_relative_terminal_children
#print axioms relative_prepared_bill
#print axioms relative_prepared_contraction
end J6R25PreparedSupply

