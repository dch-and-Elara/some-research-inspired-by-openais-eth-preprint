import J6R50IntegrationSameRun

/-! Size-independent termination and occurrence-based fee accounting
starting at the actual absolute depth of the selected packed call. -/
namespace J6R51
open scoped Polynomial BigOperators
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R49Cost J6R50Integration J6R16ModeCost

open J6R32StatefulArithmetic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3300
set_option maxHeartbeats 11000000

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
variable (r : Call (PhysicalHost f ell))

include cfg in
theorem no_scoped_occurrence_beyond_absolute_depth
    (stable : Stable s C r) (fit : r.depth ≤ pathLimit s C) :
    occurrences (nativeScopedPlan sel r) ⟨r,Path.root⟩ (pathLimit s C-r.depth+1) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro z hz
  have hp : z.1 ∈ (occurrences (nativeScopedPlan sel r) ⟨r,Path.root⟩
      (pathLimit s C-r.depth+1)).map Sigma.fst := List.mem_map_of_mem hz
  change z.1 ∈ (occurrences (scopePlan (Plan sel) (Path sel r)
    (fun x w => Path.step x.2 w)) ⟨r,Path.root⟩ (pathLimit s C-r.depth+1)).map Sigma.fst at hp
  rw [scope_occurrences_project] at hp
  obtain ⟨reach,dep⟩ := occurrence_reach_depth (Plan sel) (fun c => c.depth)
    (fun _ _ => rfl) r (pathLimit s C-r.depth+1) z.1 hp
  have bound := stable_path_depth_bound_from_start cfg sel reach stable fit
  omega

include cfg in
theorem paid_run_from_absolute_depth
    (stable : Stable s C r) (fit : r.depth ≤ pathLimit s C)
    (total localFee : Sigma (Path sel r) → ℕ)
    (steps : ∀ z, total z ≤ localFee z +
      ((childList (nativeScopedPlan sel r) z).map total).sum) :
    total ⟨r,Path.root⟩ ≤ ∑ j ∈ Finset.range (pathLimit s C-r.depth+1),
      levelBill (nativeScopedPlan sel r) ⟨r,Path.root⟩ localFee j :=
  scoped_occurrence_ledger_le (nativeScopedPlan sel r) ⟨r,Path.root⟩ total localFee
    (pathLimit s C-r.depth) (fun _ z _ => steps z)
    (no_scoped_occurrence_beyond_absolute_depth cfg sel r stable fit)

#print axioms no_scoped_occurrence_beyond_absolute_depth
#print axioms paid_run_from_absolute_depth
end J6R51
