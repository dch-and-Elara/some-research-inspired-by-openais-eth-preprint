
import P5HybridClosurePrintedEnd
import P5HybridClosurePrintedInterpolation

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false

/-! No enlargement of the published MAIN deformation/interpolation
parameters is used for the extra tie. -/
namespace Paper5.HybridMainOnly
open scoped Classical Topology
open Filter Paper5.HybridClosure Paper5.HybridClosure.Printed
noncomputable section

structure PrintedMainOnlyReady (N : ℕ) : Prop where
  alphabet : 32≤mainR N
  twoNodes : 2≤mainQ N
  oldLayout : 12*(mainCells N)^2≤4*N
  newLayout : 2*5*(mainCells N)^2≤12*N
  groups : 2*mainQ N*(mainR N)^2≤4*N
  multiple : 32≤mainMultiplicity N
  degreeFit : 6*mainMultiplicity N≤mainQ N

theorem printed_main_only_eventual :
    ∀ᶠ N : ℕ in atTop, PrintedMainOnlyReady N := by
  filter_upwards [main_printed_eventual,main_interpolation_tuning_eventual] with N hM hI
  refine ⟨hM.1,by omega,hM.2.2.1,?_,hM.2.2.2,hI.1,hI.2⟩
  have h0 : 2*5*(mainCells N)^2≤12*(mainCells N)^2 :=
    Nat.mul_le_mul_right _ (by decide)
  exact h0.trans (hM.2.2.1.trans (by omega))

theorem main_only_two_node_indices (N : ℕ) (t u : Fin (mainQ N)) (tu : t≠u) :
    1≤t.val+1 ∧ t.val+1≤mainQ N ∧ 1≤u.val+1 ∧ u.val+1≤mainQ N ∧ t.val+1≠u.val+1 := by
  have hv : t.val≠u.val := fun h=>tu (Fin.ext h)
  omega

theorem main_only_linear_scan_cost (N : ℕ) (hN : 0<N) (ready : PrintedMainOnlyReady N) :
    6*N+2*mainR N+1≤8*N+1 := by
  have h := word_time_linear_of_source_feasible N (mainQ N) (mainR N) hN
    (by have := ready.twoNodes; omega) ready.groups
  omega


#print axioms printed_main_only_eventual
#print axioms main_only_two_node_indices
#print axioms main_only_linear_scan_cost
end
end Paper5.HybridMainOnly