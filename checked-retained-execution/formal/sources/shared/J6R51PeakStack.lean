
import J6R51PeakDirectory
import J6R51PeakNativeHeader
import J6R50PeakStartPrecision
import J6R48DFSScope

/-! Geometric lifetime of actual descriptor fields on the same
typed source stack. New descriptor rows sum to spawned edges, not
to the number of possible calls or to all 64 groups. -/
namespace J6R51Peak
open scoped Polynomial
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R30ProducedGateRegistry J6R32StatefulArithmetic
open J6R33StatefulArithmeticPage J6R48DFS J6R50Peak

set_option autoImplicit false
set_option maxHeartbeats 13500000
set_option maxRecDepth 3300

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "L" => PageBank f ell key prec tw bw page

def SourceHeaderFit (born : Births T key prec tw bw page) (fixed port body : ℕ) : Prop :=
  ∀ {x : Call (PhysicalHost f ell)} (p : Path sel r x) (w : (Plan sel).Slot x),
    let B := born p w
    fixedWords B≤fixed ∧ B.port+6≤port ∧
      ∀ row∈selectedSourceRows B,row.body.length≤body

noncomputable def spawnedEdgeSum : {x : Call (PhysicalHost f ell)} → Path sel r x → ℕ
  | _,.root => 0
  | _,.step (c:=x) p w => spawnedEdgeSum p+((Plan sel).child x w).edges

theorem spawned_edges_are_exact_suffix (p : Path sel r c) :
    (edgeStack p).sum=r.edges+spawnedEdgeSum p := by
  induction p with
  | root => simp [edgeStack,spawnedEdgeSum]
  | step p w ih =>
    simp only [edgeStack,spawnedEdgeSum,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero,ih,Nat.add_assoc]

theorem spawned_edges_geometric (p : Path sel r c) : spawnedEdgeSum p≤3*r.edges/29 := by
  have geom := edgeStack_geometric p
  rw [spawned_edges_are_exact_suffix p] at geom
  omega

def fixedInsertion (key prec tw bw fixed : ℕ) : ℕ := 3*key+prec+1+tw+bw+2*fixed

def descriptorBudget (initial : L) (rootEdges depth fixed port body : ℕ) : ℕ :=
  directoryBits initial+depth*fixedInsertion key prec tw bw fixed+
    (3*rootEdges/29)*(2*(port+body))

theorem actual_descriptor_stack_bits (born : Births T key prec tw bw page)
    (initial : L) (fixed port body : ℕ) (fit : SourceHeaderFit born fixed port body)
    (p : Path sel r c) :
    directoryBits (stackBank born initial p)≤
      directoryBits initial+moves p*fixedInsertion key prec tw bw fixed+
        spawnedEdgeSum p*(2*(port+body)) := by
  induction p with
  | root => simp [stackBank,moves,spawnedEdgeSum]
  | @step x p w ih =>
    let B := born p w
    obtain ⟨h,k,t⟩ := fit p w
    have bytes := actual_child_header_width B fixed port body h k t
    have localBill :
        insertionBits B.job≤fixedInsertion key prec tw bw fixed+
          ((Plan sel).child x w).edges*(2*(port+body)) := by
      unfold insertionBits fixedInsertion
      have z := Nat.mul_le_mul_left 2 bytes
      change 2*B.job.entry.result.bytes.length≤2*(fixed+((Plan sel).child x w).edges*(port+body)) at z
      rw [Nat.mul_add,←Nat.mul_assoc,Nat.mul_comm 2 ((Plan sel).child x w).edges,Nat.mul_assoc] at z
      omega
    rw [stackBank,one_publication_adds_exact_directory_bits]
    simp only [moves,spawnedEdgeSum,Nat.add_mul,Nat.one_mul]
    exact (Nat.add_le_add ih localBill).trans_eq (by ac_rfl)

theorem bounded_descriptor_stack_at_original_start (born : Births T key prec tw bw page)
    (initial : L) (fixed port body : ℕ) (fit : SourceHeaderFit born fixed port body)
    (p : Path sel r c) :
    directoryBits (stackBank born initial p)≤
      descriptorBudget initial r.edges (pathLimit s C) fixed port body := by
  apply (actual_descriptor_stack_bits born initial fixed port body fit p).trans
  exact Nat.add_le_add (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (actual_ancestry_moves_any_start cfg sel T.rootStable p)) _)
    (Nat.mul_le_mul_right _ (spawned_edges_geometric p))

theorem next_descriptor_fits_geometric_cap (born : Births T key prec tw bw page)
    (fixed port body : ℕ) (fit : SourceHeaderFit born fixed port body)
    (p : Path sel r c) (w : (Plan sel).Slot c) :
    (born p w).job.entry.result.bytes.length≤fixed+(3*r.edges/29)*(port+body) := by
  have z := spawned_edges_geometric (Path.step p w)
  change spawnedEdgeSum p+((Plan sel).child c w).edges≤3*r.edges/29 at z
  have childBound : (p.ticket w).child.edges≤3*r.edges/29 := by
    change ((Plan sel).child c w).edges≤3*r.edges/29
    omega
  obtain ⟨h,k,t⟩ := fit p w
  exact (actual_child_header_width (born p w) fixed port body h k t).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ childBound) _)

theorem live_headers_fit_same_geometric_cap (born : Births T key prec tw bw page)
    (initial : L) (fixed port body : ℕ) (fit : SourceHeaderFit born fixed port body)
    (U : ℕ) (rootFit : ∀ row∈initial.headers,row.bytes.length≤U)
    (p : Path sel r c) :
    ∀ row∈(stackBank born initial p).headers,row.bytes.length≤
      max U (fixed+(3*r.edges/29)*(port+body)) := by
  induction p with
  | root =>
    intro row hx
    exact (rootFit row hx).trans (le_max_left _ _)
  | step p w ih =>
    intro row hx
    change row∈(born p w).job.entry.result::(stackBank born initial p).headers at hx
    rcases List.mem_cons.mp hx with eq | hx
    · subst row
      exact (next_descriptor_fits_geometric_cap born fixed port body fit p w).trans (le_max_right _ _)
    · exact ih row hx

#print axioms spawned_edges_are_exact_suffix
#print axioms spawned_edges_geometric
#print axioms actual_descriptor_stack_bits
#print axioms bounded_descriptor_stack_at_original_start
#print axioms next_descriptor_fits_geometric_cap
#print axioms live_headers_fit_same_geometric_cap
end J6R51Peak
