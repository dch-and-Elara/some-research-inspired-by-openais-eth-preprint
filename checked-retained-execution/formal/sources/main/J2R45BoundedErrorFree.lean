
import QueryBounds

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 950000
set_option linter.unusedSectionVars false

/-! Free queries with a single fixed reply can be eliminated before
truncating the actual paid path. No bound on the unreachable zero path
of the original strategy is assumed. -/
namespace J2R45BoundedError
open scoped Classical BigOperators
open FiniteWeightedQueryTree

variable {Q R W Seed : Type*}

def mainOnly (zero : R) (counted : Q→Bool) :
    DecisionTree Q R→DecisionTree Q R
  | .leaf b => .leaf b
  | .ask q next =>
    if counted q then .ask q (fun r=>mainOnly zero counted (next r))
    else mainOnly zero counted (next zero)

def mainCharge (counted : Q→Bool) (q : Q) : ℕ := (counted q).toNat

theorem elimination_exact (zero : R) (counted : Q→Bool) (oracle : Q→R)
    (freeConstant : ∀ q,counted q=false → oracle q=zero) (tree : DecisionTree Q R) :
    evaluate oracle (mainOnly zero counted tree)=evaluate oracle tree ∧
    paid (fun _=>1) oracle (mainOnly zero counted tree)=paid (mainCharge counted) oracle tree := by
  induction tree with
  | leaf b => exact ⟨rfl,rfl⟩
  | ask q next ih =>
    cases h : counted q
    · have hz := freeConstant q h
      simpa only [mainOnly,h,if_false,Bool.false_eq_true,not_false_eq_true,paid,evaluate,
        mainCharge,Bool.toNat_false,zero_add,hz] using ih zero
    · simpa only [mainOnly,h,if_true,paid,evaluate,mainCharge,Bool.toNat_true,ih] using
        (show evaluate oracle (mainOnly zero counted (next (oracle q)))=
            evaluate oracle (next (oracle q)) ∧
          1+paid (fun _=>1) oracle (mainOnly zero counted (next (oracle q)))=
            1+paid (mainCharge counted) oracle (next (oracle q)) from
          ⟨(ih (oracle q)).1,congrArg (1+·) (ih (oracle q)).2⟩)

theorem finite_seed_bound_with_free_answers [DecidableEq W] (zero : R)
    (oracle : W→Bool→Q→R) (support : Q→Finset W)
    (off : ∀ w b q,w∉support q → oracle w b q=zero)
    (counted : Q→Bool) (freeConstant : ∀ w b q,counted q=false → oracle w b q=zero)
    (capacity : ℕ) (cap : ∀ q,(support q).card≤capacity)
    (seeds : Finset Seed) (hs : seeds.Nonempty) (tree : Seed→DecisionTree Q R)
    (pool : Finset W) (T : ℕ)
    (bound : ∀ s∈seeds,∀ w∈pool,∀ b,paid (mainCharge counted) (oracle w b) (tree s)≤T)
    (success : ∀ w∈pool,∀ b : Bool,2*seeds.card≤
      3*∑ s ∈ seeds,if evaluate (oracle w b) (tree s)=b then 1 else 0) :
    pool.card≤3*(capacity*T) := by
  apply randomized_query_capacity zero oracle support off capacity cap seeds hs
    (fun s=>mainOnly zero counted (tree s)) pool T
  · intro s hs' w hw b
    rw [(elimination_exact zero counted _ (freeConstant w b) (tree s)).2]
    exact bound s hs' w hw b
  · intro w hw b
    simpa only [(elimination_exact zero counted _ (freeConstant w b) (tree _)).1] using success w hw b

theorem remove_capacity_factor (k k₀ T : ℕ) (hk : k₀≤k)
    (h : 2^k≤3*((2^(k-k₀))*T)) : 2^k₀≤3*T := by
  have he : (2:ℕ)^k=(2:ℕ)^k₀*2^(k-k₀) := by rw [←pow_add,Nat.add_sub_of_le hk]
  have hu : (2:ℕ)^k₀*2^(k-k₀)≤(3*T)*2^(k-k₀) := by
    calc
      _ = 2^k := he.symm
      _ ≤ _ := h
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_right hu (by positivity)

#print axioms elimination_exact
#print axioms finite_seed_bound_with_free_answers
#print axioms remove_capacity_factor
end J2R45BoundedError
