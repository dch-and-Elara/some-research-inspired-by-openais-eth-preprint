import J6R33OriginalJ6Sizes
import J6ChildPlan

/-! Executable counting for the constant-universe inputs excluded by
the printed active branch, including n=0 and empty or repeated clauses. -/
namespace J6R33OriginalJ6
open scoped BigOperators
open Std.Sat J6ChildPlan J6Mesh J6R28GeneratedRootFrame J7R10Readout

def smallBranchCount {n : ℕ} (F : CNF (Fin n)) : ℕ :=
  allBits n (fun x=>if F.eval x=true then 1 else 0)

theorem small_branch_exact {n : ℕ} (F : CNF (Fin n)) :
    smallBranchCount F=PinnedCNF.modelCount F := by
  classical
  unfold smallBranchCount PinnedCNF.modelCount
  rw [allBits_exact,Finset.card_filter]
  apply Finset.sum_congr
  · ext x; simp
  · intro x _; by_cases h : F.eval x=true <;> simp [h]

theorem small_branch_assignments {n : ℕ} (F : CNF (Fin n))
    (three : ∀ c∈F,c.length≤3)
    (bad : Nat.clog 2 (physicalSize (mCNF F) (literalNativeSize F)) < activeFloor)
    (bound : ℕ) (largeConstant : 2^activeFloor≤bound) :
    smallBranchCount F=PinnedCNF.modelCount F ∧
      allBits n (fun _=>(1:ℕ))=2^n ∧ 2^n≤(2:ℕ)^bound := by
  refine ⟨small_branch_exact F,allBits_visits n,?_⟩
  cases n with
  | zero =>
    simp only [pow_zero]
    exact Nat.succ_le_of_lt (by positivity : 0<(2:ℕ)^bound)
  | succ n =>
    letI : Nonempty (Fin (n+1)) := ⟨0⟩
    have C := small_inputs_have_bounded_universe F three bad
    rw [Fintype.card_fin] at C
    have h : n+1≤bound := (Nat.le_add_right _ 2).trans (C.le.trans largeConstant)
    exact Nat.pow_le_pow_right (by decide) h

#print axioms small_branch_exact
#print axioms small_branch_assignments
end J6R33OriginalJ6
