import J6R24MeteredRecursionActiveValue
import J6R24MeteredRecursionTreeLedger

/-! Whole-recursion claim on prepared descriptors. The reference is exactly
the R12 printed source program on the same native call tree. The witness
is a single recursively evaluated measured frame, not a separately
supplied VM trace, precomputed response family, or assumed final value. -/
namespace J6R24MeteredRecursion
open scoped Polynomial BigOperators
open Polynomial A1R10 AOracleMachineTime
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost J6R21Ancestor

variable {f : ℤ[X]} {ell s C : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
variable (T : Prepared cfg sel r hf)
variable [env : DecidableEq (Envelope (N sel) (Childs sel) r)]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

set_option maxHeartbeats 6500000 in
theorem Prepared.correctAt (c : Call (PhysicalHost f ell)) (hc : NativeReach (Plan sel) r c) :
    (T.frame hc).decode (T.run c hc).result=(J6R12Blueprint.sourceBlueprint sel r hf).program.run c := by
  by_cases h : c.edges≤(S).cutoff
  · rw [T.run_leaf hc h]
    have he : 0<f.natDegree := (T.frame hc).natDegree hf ▸ (T.frame hc).sizePos
    exact (convertLeaf_receipt he (T.leaf c hc h) (T.frame hc)).1.trans
      (encoded_leaf_is_source_stop sel r hf T.leaf c hc h)
  · let ha := Nat.lt_of_not_ge h
    let d := ready_reachable cfg sel hc T.rootStable ha
    rw [T.run_active hc ha]
    let D := T.active c hc ha
    let go := T.childRuns hc d
    have exactChild (t : Center S c) (z : Probe S c) (β : NativeMenu (N sel) c t) (g : Fin 64) :
        (T.bank (registerPrecision S c t) (register_positive d t)).decode (go t z β g).result=
          (J6R12Blueprint.sourceBlueprint sel r hf).program.run
            ((Plan sel).child c ⟨⟨t,z,β,g⟩,d.active⟩) := by
      let w := addressed (sel:=sel) d t z β g
      exact Prepared.correctAt _ (reach_snoc (Plan sel) hc w)
    obtain ⟨x,_,hWord,hDec⟩ := actual_active_decoded cfg sel r hf hc d T.rootStable D
      (reachable_positive T hc) T.vPositive go exactChild
    change (T.frame hc).decode (D.eval (reachable_positive T hc) T.vPositive hf go).result=_
    rw [hWord]
    exact hDec
termination_by c.edges
decreasing_by exact (Plan sel).smaller c w

set_option maxHeartbeats 3200000 in
theorem Prepared.no_strip_failure {c : Call (PhysicalHost f ell)} (hc : NativeReach (Plan sel) r c)
    (ha : (S).cutoff<c.edges) :
    let d := ready_reachable cfg sel hc T.rootStable ha
    ∃ x,((T.active c hc ha).finish (reachable_positive T hc) T.vPositive hf
      (T.childRuns hc d)).result=some x := by
  let d := ready_reachable cfg sel hc T.rootStable ha
  let D := T.active c hc ha
  let go := T.childRuns hc d
  have e (t : Center S c) (z : Probe S c) (β : NativeMenu (N sel) c t) (g : Fin 64) :
      (T.bank (registerPrecision S c t) (register_positive d t)).decode (go t z β g).result=
        (J6R12Blueprint.sourceBlueprint sel r hf).program.run ((Plan sel).child c ⟨⟨t,z,β,g⟩,d.active⟩) := by
    let w := addressed (sel:=sel) d t z β g
    exact T.correctAt _ (reach_snoc (Plan sel) hc w)
  obtain ⟨x,h,_,_⟩ := actual_active_decoded cfg sel r hf hc d T.rootStable D
    (reachable_positive T hc) T.vPositive go e
  exact ⟨x,h⟩

/-- Exact native semantic value and exact occurrence ledger for the
same prepared-tree execution. This theorem does not meter preparation
of the dependent layout/registry/mode tape or decode the final count. -/
theorem whole_prepared_tree (d₀ : r.depth=0) :
    let Run := T.run r (.reflexive _)
    (T.frame (.reflexive _)).decode Run.result=(J6R12Blueprint.sourceBlueprint sel r hf).program.run r ∧
    Run.steps=∑ j∈Finset.range (pathLimit s C+1),levelBill (Plan sel) r T.localAt j :=
  ⟨T.correctAt r (.reflexive _),T.paid_exact d₀⟩

set_option maxHeartbeats 3000000 in
theorem whole_prepared_contraction (d₀ : r.depth=0) :
    let Run := T.run r (.reflexive _)
    (T.frame (.reflexive _)).decode Run.result=reduce r.prec f ell (r.host.contract hf) ∧
    Run.steps=∑ j∈Finset.range (pathLimit s C+1),levelBill (Plan sel) r T.localAt j := by
  have e : env=sourceDecision sel r := Subsingleton.elim _ _
  subst env
  letI : DecidableEq (Envelope (N sel) (Childs sel) r) := sourceDecision sel r
  let G := T.frame (NativeReach.reflexive r)
  have he : 0<f.natDegree := G.natDegree hf ▸ G.sizePos
  obtain ⟨value,cost⟩ := whole_prepared_tree T d₀
  exact ⟨value.trans (J6R12Integral.printed_run_exact cfg sel r T.rootStable hf he),cost⟩

#print axioms Prepared.correctAt
#print axioms Prepared.no_strip_failure
#print axioms whole_prepared_tree
#print axioms whole_prepared_contraction
end J6R24MeteredRecursion
