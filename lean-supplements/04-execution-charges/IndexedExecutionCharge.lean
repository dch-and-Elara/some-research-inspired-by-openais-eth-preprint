import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

/-! Finite execution charges indexed by occurrences, not by event labels. -/

namespace RootSeparation.IndexedExecutionCharge

open scoped BigOperators

/-- An n-point injective image of individually charged steps accounts for
at least n units. Charges at other positions are allowed to be zero. -/
theorem embedded_count_le_charge {n m : ℕ} (charge : Fin m → ℕ)
    (embed : Fin n → Fin m) (injective : Function.Injective embed)
    (unit : ∀ i, 1 ≤ charge (embed i)) :
    n ≤ ∑ j, charge j := by
  classical
  have h : n ≤ ∑ i : Fin n, charge (embed i) := by
    simpa using Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
      (f := fun _ => (1 : ℕ)) (g := fun i => charge (embed i)) (fun i _ => unit i)
  calc
    n ≤ ∑ i : Fin n, charge (embed i) := h
    _ = ∑ j ∈ Finset.univ.image embed, charge j :=
      (Finset.sum_image (fun _ _ _ _ heq => injective heq)).symm
    _ ≤ ∑ j, charge j := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun j _ _ => Nat.zero_le (charge j))

#print axioms embedded_count_le_charge

end RootSeparation.IndexedExecutionCharge
