import J6R25PreparedSupplyFundedRun

/-! Exact addition of the actual mode preparation to the same R24
recursion ledger. Fees are taken from the producer executed at each
centre, never from a freely supplied per-node charge. Failed arbitrary
physical directory/layout installation is not hidden in this theorem. -/
namespace J6R25PreparedSupply
open scoped Polynomial BigOperators Classical
open Polynomial A1R10 AOracleMachineTime
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J1PPrinted J6R24MeteredRecursion

variable {f : ℤ[X]} {ell s C : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
variable (T : Input cfg sel r hf)

noncomputable def Input.modeAt (c : Call (PhysicalHost f ell)) : ℕ :=
  if h : NativeReach (Plan sel) r c then
    if ha : (S).cutoff<c.edges then T.modeFee h (T.geometry c h ha) else 0
  else 0

noncomputable def Input.costAt (c : Call (PhysicalHost f ell)) : ℕ :=
  if h : NativeReach (Plan sel) r c then (T.run c h).steps else 0

set_option maxHeartbeats 5000000 in
theorem Input.correct_charge {c : Call (PhysicalHost f ell)} (hc : NativeReach (Plan sel) r c) :
    T.costAt c=(T.prepared.localAt c+T.modeAt c)+((childList (Plan sel) c).map T.costAt).sum := by
  by_cases hl : c.edges≤(S).cutoff
  · rw [Input.costAt,dif_pos hc,T.run_leaf hc hl,Prepared.localAt,dif_pos hc,dif_pos hl,
      Input.modeAt,dif_pos hc,dif_neg (Nat.not_lt_of_ge hl),leaf_has_no_child hl]
    simp only [List.map_nil,List.sum_nil,Nat.add_zero]
    rfl
  · let ha := Nat.lt_of_not_ge hl
    let d := ready_reachable cfg sel hc T.rootStable ha
    let I := T.geometry c hc ha
    let D := T.activeDesc hc I
    let hp := reachable_positive T.prepared hc
    let P := T.prepared.childRuns hc d
    let go := T.childRuns hc d
    have step := (D.one_visit hp T.vPositive hf go).fee
    have mode := (T.funded_extra_exact hc I hp go).fee
    have bareEq : (fun t z β g=>bare (go t z β g))=(fun t z β g=>bare (P t z β g)) := by
      funext t z β g
      let w := addressed (sel:=sel) d t z β g
      have he := T.same_raw ((Plan sel).child c w) (reach_snoc (Plan sel) hc w)
      change (Meter.mk (T.run ((Plan sel).child c w) _).result 0) =
        (Meter.mk (T.prepared.run ((Plan sel).child c w) _).result 0)
      rw [he]
    rw [bareEq] at step
    have nested := child_sum_exact d D T.vPositive go (T.costAt ∘ (Plan sel).child c)
      (fun t z β g=>by
        let w := addressed (sel:=sel) d t z β g
        change (T.run ((Plan sel).child c w) (reach_snoc (Plan sel) hc w)).steps
          =T.costAt ((Plan sel).child c w)
        unfold Input.costAt
        rw [dif_pos (reach_snoc (Plan sel) hc w)])
    rw [Input.costAt,dif_pos hc,T.run_active hc ha,Prepared.localAt,dif_pos hc,dif_neg hl,
      Input.modeAt,dif_pos hc,dif_pos ha,childList_bill_as_sum,←nested]
    change (T.fundedEval hc I hp go).steps =
      ((D.eval hp T.vPositive hf (fun t z β g=>bare (P t z β g))).steps+T.modeFee hc I)+D.children T.vPositive go
    rw [mode,step]
    omega

theorem Input.generation_is_paid (T : Input cfg sel r hf) :
    (T.run r (.reflexive _)).steps=(T.prepared.run r (.reflexive _)).steps+
      ∑ j∈Finset.range (pathLimit s C+1),levelBill (Plan sel) r T.modeAt j := by
  have atRoot : T.costAt r=(T.run r (.reflexive _)).steps := by
    unfold Input.costAt
    rw [dif_pos (NativeReach.reflexive r)]
  rw [←atRoot,T.prepared.paid_exact T.dZero]
  rw [occurrence_tree_ledger (Plan sel) r T.costAt (fun c=>T.prepared.localAt c+T.modeAt c)
    (pathLimit s C) (fun j c hm=>T.correct_charge (exact_depth_occurrence sel T.dZero j c hm).1)
    (no_occurrences_past_bound cfg sel T.rootStable T.dZero _ (Nat.lt_succ_self _))]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  exact list_charge (occurrences (Plan sel) r k) _ _ _ (fun _ _=>rfl)

variable [DecidableEq (Envelope (N sel) (Childs sel) r)]
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem whole_produced_modes :
    let R := T.run r (.reflexive _)
    (T.prepared.frame (.reflexive _)).decode R.result=reduce r.prec f ell (r.host.contract hf) ∧
    R.steps=(T.prepared.run r (.reflexive _)).steps+
      ∑ j∈Finset.range (pathLimit s C+1),levelBill (Plan sel) r T.modeAt j := by
  dsimp only
  rw [T.same_raw r (.reflexive _)]
  exact ⟨(whole_prepared_contraction T.prepared T.dZero).1,T.generation_is_paid⟩

#print axioms Input.correct_charge
#print axioms Input.generation_is_paid
#print axioms whole_produced_modes
end J6R25PreparedSupply

