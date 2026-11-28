import J6R24MeteredRecursionRun
import J6R16ModeCostBranchFold

/-! The actual recursive program's instrumented meter telescopes to its
own local charges. A bare child receipt in the computation of a local
charge means "the same previously counted returned word", not "a new
computation free of charge"; `one_visit` proves the exact subtraction. -/
namespace J6R24MeteredRecursion
open scoped Polynomial BigOperators Classical
open Polynomial A1R10 AOracleMachineTime
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost

variable {f : ℤ[X]} {ell s C : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
variable (T : Prepared cfg sel r hf)

noncomputable def Prepared.totalAt (c : Call (PhysicalHost f ell)) : ℕ :=
  if hc : NativeReach (Plan sel) r c then (T.run c hc).steps else 0

noncomputable def Prepared.localAt (c : Call (PhysicalHost f ell)) : ℕ :=
  if hc : NativeReach (Plan sel) r c then
    if h : c.edges≤(S).cutoff then (convertLeaf (T.leaf c hc h) (T.frame hc)).steps else
      let ha := Nat.lt_of_not_ge h
      let d := ready_reachable cfg sel hc T.rootStable ha
      let D := T.active c hc ha
      let go := T.childRuns hc d
      (D.eval (reachable_positive T hc) T.vPositive hf
        (fun t z β g=>bare (go t z β g))).steps
  else 0

set_option maxHeartbeats 3600000 in
theorem Prepared.node_bill {c : Call (PhysicalHost f ell)} (hc : NativeReach (Plan sel) r c) :
    T.totalAt c=T.localAt c+((childList (Plan sel) c).map T.totalAt).sum := by
  by_cases hl : c.edges≤(S).cutoff
  · rw [Prepared.totalAt,dif_pos hc,Prepared.localAt,dif_pos hc,dif_pos hl,
      leaf_has_no_child hl,T.run_leaf hc hl]
    rfl
  · let ha := Nat.lt_of_not_ge hl
    let d := ready_reachable cfg sel hc T.rootStable ha
    let D := T.active c hc ha
    let go := T.childRuns hc d
    have step := (D.one_visit (reachable_positive T hc) T.vPositive hf go).fee
    have nested := child_sum_exact d D T.vPositive go (T.totalAt ∘ (Plan sel).child c)
      (fun t z β g=>by
        let w := addressed (sel:=sel) d t z β g
        change (T.run ((Plan sel).child c w) (reach_snoc (Plan sel) hc w)).steps
          =T.totalAt ((Plan sel).child c w)
        unfold Prepared.totalAt
        rw [dif_pos (reach_snoc (Plan sel) hc w)])
    rw [Prepared.totalAt,dif_pos hc,T.run_active hc ha,Prepared.localAt,dif_pos hc,dif_neg hl,
        childList_bill_as_sum]
    change _= _+_
    rw [←nested]
    exact step

theorem Prepared.paid_exact (d₀ : r.depth=0) :
    (T.run r (.reflexive _)).steps =
      ∑ j∈Finset.range (pathLimit s C+1),levelBill (Plan sel) r T.localAt j := by
  have atRoot : T.totalAt r=(T.run r (.reflexive _)).steps := by
    unfold Prepared.totalAt
    rw [dif_pos (NativeReach.reflexive r)]
  rw [←atRoot]
  exact occurrence_tree_ledger (Plan sel) r T.totalAt T.localAt (pathLimit s C)
    (fun j c hm=>T.node_bill (exact_depth_occurrence sel d₀ j c hm).1)
    (no_occurrences_past_bound cfg sel T.rootStable d₀ _ (Nat.lt_succ_self _))

#print axioms Prepared.node_bill
#print axioms Prepared.paid_exact
end J6R24MeteredRecursion
