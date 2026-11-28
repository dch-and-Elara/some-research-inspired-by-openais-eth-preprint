import Mathlib.Tactic
set_option warningAsError true
namespace Paper5.OuterCenters
open scoped BigOperators
theorem fiber_no_decoder {I X : Type*} {A : I → Type*}
    (observe : X → ∀ i, A i) (target : X → ℕ) (x y : X)
    (same : ∀ i, observe x i = observe y i) (different : target x ≠ target y) :
    ¬ ∃ decode : (∀ i, A i) → ℕ, ∀ z, decode (observe z) = target z := by
  rintro ⟨decode, correct⟩
  exact different ((correct x).symm.trans ((congrArg decode (funext same)).trans (correct y)))

theorem child_fiber_implies_product_fiber {R G : Type*} [CommMonoid R] [Fintype G]
    (a b : G → R) (same : ∀ g, a g = b g) : (∏ g, a g) = ∏ g, b g := by
  exact congrArg (fun k : G → R => ∏ g, k g) (funext same)

#print axioms fiber_no_decoder
#print axioms child_fiber_implies_product_fiber
end Paper5.OuterCenters
