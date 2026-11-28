import J6R32StatefulArithmeticWhole

/-! The source's actual depth bound controls the additive local
arithmetic part. Dynamic leaf and directory costs remain distinguishable
and are accounted for by the separate live-state ledger. -/
namespace J6R32StatefulArithmetic
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R10 A1R12
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable
open J6R11Blueprint J6R12Blueprint J1PPrinted J6R16ModeCost
open J6R21Ancestor J6R24MeteredRecursion J6R30ProducedGateRegistry

variable {f : ℤ[X]} {ell s C key prec tw bw : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)

variable (T : Prepared cfg sel r hf)
noncomputable def referenceAt (c : Call (PhysicalHost f ell)) : ℕ :=
  if h : NativeReach (Plan sel) r c then (reference T c h).steps else 0

noncomputable def activeArithmetic (c : Call (PhysicalHost f ell)) : ℕ :=
  if c.edges≤(S).cutoff then 0 else T.localAt c

variable [DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) r)]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem equal_reference_word (c : Call (PhysicalHost f ell)) (h : NativeReach (Plan sel) r c) :
    (reference T c h).result=(T.run c h).result :=
  frame_words_injective hf (T.frame h) ((reference_source T c h).trans (T.correctAt c h).symm)

set_option maxHeartbeats 6000000 in
theorem reference_node_bill {c : Call (PhysicalHost f ell)} (hc : NativeReach (Plan sel) r c) :
    referenceAt T c=activeArithmetic T c+((childList (Plan sel) c).map (referenceAt T)).sum := by
  by_cases hl : c.edges≤(S).cutoff
  · rw [referenceAt,dif_pos hc,activeArithmetic,if_pos hl,leaf_has_no_child hl,reference_leaf hc hl]
    rfl
  · let ha := Nat.lt_of_not_ge hl
    let d := ready_reachable cfg sel hc T.rootStable ha
    let D := T.active c hc ha
    let go : ActiveChild (sel:=sel) (d:=d) T.bank := fun t z β g=>
      let w := addressed (sel:=sel) d t z β g
      reference T ((Plan sel).child c w) (reach_snoc (Plan sel) hc w)
    let live := T.childRuns hc d
    have eq : (fun t z β g=>bare (go t z β g))=(fun t z β g=>bare (live t z β g)) := by
      funext t z β g
      let w := addressed (sel:=sel) d t z β g
      exact congrArg (fun x=>(⟨x,0⟩ : Meter _))
        (equal_reference_word T ((Plan sel).child c w) (reach_snoc (Plan sel) hc w))
    have step := (D.one_visit (reachable_positive T hc) T.vPositive hf go).fee
    have nested := child_sum_exact d D T.vPositive go (referenceAt T ∘ (Plan sel).child c)
      (fun t z β g=>by
        let w := addressed (sel:=sel) d t z β g
        change (reference T ((Plan sel).child c w) (reach_snoc (Plan sel) hc w)).steps=
          referenceAt T ((Plan sel).child c w)
        unfold referenceAt
        rw [dif_pos (reach_snoc (Plan sel) hc w)])
    rw [referenceAt,dif_pos hc,reference,dif_neg hl,activeArithmetic,if_neg hl,
      Prepared.localAt,dif_pos hc,dif_neg hl,childList_bill_as_sum]
    change (D.eval (reachable_positive T hc) T.vPositive hf go).steps=
      (D.eval (reachable_positive T hc) T.vPositive hf (fun t z β g=>bare (live t z β g))).steps+_
    rw [←nested,←eq]
    exact step

theorem reference_depth_sum (d₀ : r.depth=0) :
    (reference T r (.reflexive r)).steps=
      ∑ j∈Finset.range (pathLimit s C+1),levelBill (Plan sel) r (activeArithmetic T) j := by
  have atRoot : referenceAt T r=(reference T r (.reflexive r)).steps := by
    unfold referenceAt
    rw [dif_pos (NativeReach.reflexive r)]
  rw [←atRoot]
  exact occurrence_tree_ledger (Plan sel) r (referenceAt T) (activeArithmetic T) (pathLimit s C)
    (fun j c hm=>reference_node_bill T (exact_depth_occurrence sel d₀ j c hm).1)
    (no_occurrences_past_bound cfg sel T.rootStable d₀ _ (Nat.lt_succ_self _))

theorem whole_live_depth (R : Resident T key prec tw bw) (d₀ : r.depth=0)
    (B : AnyLedger f ell key prec tw bw) (ready : JobsReady B (nativeLog R r .root).jobs)
    (live : R.rootLive B) :
    let out := native R r .root B
    let log := nativeLog R r .root
    (T.frame (.reflexive r)).decode out.result.1=reduce r.prec f ell (r.host.contract hf) ∧
      out.result.2=afterJobs B log.jobs ∧
      out.steps=(∑ j∈Finset.range (pathLimit s C+1),levelBill (Plan sel) r (activeArithmetic T) j)+
        chronologicalBill B log.jobs+log.extras B := by
  obtain ⟨word,state,fee⟩ := whole_live_subtree R r .root B ready live
  have leafWord := (whole_prepared_contraction T d₀).1
  have E := ((T.correctAt r (.reflexive r))).symm.trans leafWord
  exact ⟨word.trans E,state,fee.trans (by rw [reference_depth_sum T d₀])⟩

#print axioms equal_reference_word
#print axioms reference_node_bill
#print axioms reference_depth_sum
#print axioms whole_live_depth
end J6R32StatefulArithmetic
