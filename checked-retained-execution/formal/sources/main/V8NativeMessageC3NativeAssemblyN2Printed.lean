import V8NativeMessageC3NativeAssemblyN2Path

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

/-! A reached leaf in the true adapted physical Blueprint runs the
literal all-assignment fold with its own creation-tagged files. -/
namespace V8NativeMessage.C3.NativeAssembly
open scoped Classical Polynomial BigOperators
open Polynomial J6ActiveRun J6R10Reachable J6R12Blueprint J6R11Blueprint J6R9Recursive
noncomputable section

theorem blueprint_leaf_formula {A K : Type*} [Fintype K] [DecidableEq K]
    {S : Shape A K} {f : ℤ[X]} {ell : ℕ} (B : Blueprint S f ell) (d : Call A)
    (h : d.edges≤S.cutoff) :
    B.program.run d = J6ChildPlan.allBits d.edges (fun x =>
      reduce d.prec f ell (B.entries d x).prod) := by
  rw [Program.run]
  split
  · rfl
  · rename_i hn
    exact (hn h).elim

theorem printed_visit_count_exceeds_floor (H n : ℕ) (h : H<32*n) :
    2^(H/32)<J6ChildPlan.allBits n (fun _ => (1:ℕ)) := by
  rw [J6ChildPlan.allBits_visits]
  exact Nat.pow_lt_pow_right (by decide) (by omega)

variable {f : ℤ[X]} {ell : ℕ}
variable (N : NativeShape (PhysicalHost f ell)) (C : NativeChildren N)
variable (root : Call (PhysicalHost f ell))
variable [DecidableEq (Envelope N C root)]
variable (hw : PositiveData N C root) (hf : f.Monic)

/-- The exact native-to-adapted address equivalence, the ordinary
all-assignment leaf, and both integer forms of the numerical lower bound.
The theorem can be instantiated with the actual factory path. -/
theorem physical_terminal_at_native_path (d : Call (PhysicalHost f ell))
    (h : NativeReach (nativePlan N C) root d) (hl : d.edges≤N.params.cutoff)
    (hsize : N.params.cutoff < 32*d.edges) :
    let B := paddedBlueprint N C root hw f ell (physicalEntries hf)
    Reach B.program root d ∧
    B.program.run d = J6ChildPlan.allBits d.edges
      (fun x => reduce d.prec f ell (physicalEntries hf d x).prod) ∧
    2^(N.params.cutoff/32)<J6ChildPlan.allBits d.edges (fun _ => (1:ℕ)) ∧
    2^N.params.cutoff<(J6ChildPlan.allBits d.edges (fun _ => (1:ℕ)))^32 := by
  let B := paddedBlueprint N C root hw f ell (physicalEntries hf)
  exact ⟨(paddedBlueprint_exact_reachable N C root hw f ell (physicalEntries hf) d).mpr h,
    blueprint_leaf_formula B d hl,printed_visit_count_exceeds_floor _ _ hsize,
    actual_assignment_leaf_numeric _ _ hsize⟩

#print axioms blueprint_leaf_formula
#print axioms printed_visit_count_exceeds_floor
#print axioms physical_terminal_at_native_path
end
end V8NativeMessage.C3.NativeAssembly
