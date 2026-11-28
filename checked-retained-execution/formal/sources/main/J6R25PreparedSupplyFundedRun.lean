import J6R25PreparedSupplyFundedActive

/-! The measured recursive run includes the newly produced mode tape
inside each live activation, not as an unrelated bound outside the run.
Only the typed interpretation of bytes and dependent child metadata
are proof-level; construction of those physical metadata is separate. -/
namespace J6R25PreparedSupply
open scoped Polynomial
open Polynomial A1R10 AOracleMachineTime
open J6ActiveRun J6ActiveSchedule J6R9Recursive J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J1PPrinted J6R21Ancestor J6R24MeteredRecursion

variable {f : ℤ[X]} {ell s C : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
variable (T : Input cfg sel r hf)

set_option maxHeartbeats 4400000 in
noncomputable def Input.run (c : Call (PhysicalHost f ell)) (hc : NativeReach (Plan sel) r c) :
    Meter (Block (T.prepared.frame hc) ell) :=
  if h : c.edges≤(S).cutoff then convertLeaf (T.leaf c hc h) (T.prepared.frame hc) else
    let ha := Nat.lt_of_not_ge h
    let d := ready_reachable cfg sel hc T.rootStable ha
    T.fundedEval hc (T.geometry c hc ha) (reachable_positive T.prepared hc)
      (fun t z β g=>
        let w := addressed (sel:=sel) d t z β g
        run ((Plan sel).child c w) (reach_snoc (Plan sel) hc w))
termination_by c.edges
decreasing_by exact (Plan sel).smaller c w

noncomputable def Input.childRuns {c : Call (PhysicalHost f ell)}
    (hc : NativeReach (Plan sel) r c)
    (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c) :
    ActiveChild (sel:=sel) (d:=d) T.bank :=
  fun t z β g=>
    let w := addressed (sel:=sel) d t z β g
    T.run ((Plan sel).child c w) (reach_snoc (Plan sel) hc w)

theorem Input.run_leaf {c : Call (PhysicalHost f ell)} (hc : NativeReach (Plan sel) r c)
    (h : c.edges≤(S).cutoff) :
    T.run c hc=convertLeaf (T.leaf c hc h) (T.prepared.frame hc) := by
  rw [Input.run,dif_pos h]

theorem Input.run_active {c : Call (PhysicalHost f ell)} (hc : NativeReach (Plan sel) r c)
    (ha : (S).cutoff<c.edges) :
    T.run c hc=T.fundedEval hc (T.geometry c hc ha) (reachable_positive T.prepared hc)
      (T.childRuns hc (ready_reachable cfg sel hc T.rootStable ha)) := by
  rw [Input.run,dif_neg (Nat.not_le.mpr ha)]
  rfl

set_option maxHeartbeats 5200000 in
theorem Input.same_raw (c : Call (PhysicalHost f ell)) (hc : NativeReach (Plan sel) r c) :
    (T.run c hc).result=(T.prepared.run c hc).result := by
  by_cases h : c.edges≤(S).cutoff
  · rw [T.run_leaf hc h,T.prepared.run_leaf hc h]
    rfl
  · let ha := Nat.lt_of_not_ge h
    let d := ready_reachable cfg sel hc T.rootStable ha
    let G := T.geometry c hc ha
    let D := T.activeDesc hc G
    let hp := reachable_positive T.prepared hc
    let R := T.childRuns hc d
    let P := T.prepared.childRuns hc d
    rw [T.run_active hc ha,T.prepared.run_active hc ha]
    change (T.fundedEval hc G hp R).result=(D.eval hp T.vPositive hf P).result
    rw [(T.funded_extra_exact hc G hp R).value]
    apply active_result_congr hp D T.vPositive R P
    intro t z β g
    let w := addressed (sel:=sel) d t z β g
    exact Input.same_raw _ (reach_snoc (Plan sel) hc w)
termination_by c.edges
decreasing_by exact (Plan sel).smaller c w

#print axioms Input.run_active
#print axioms Input.same_raw
end J6R25PreparedSupply
