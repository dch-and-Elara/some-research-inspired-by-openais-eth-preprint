import SolverChildren

noncomputable section
namespace RootSeparation.Solver

open scoped BigOperators
open Classical

variable {P R : Type*} [Fintype P] [CommSemiring R]
variable {Rows Modes : P → Type*} [∀ k, Fintype (Rows k)] [∀ k, Fintype (Modes k)]

/-- Simultaneous coefficient extraction by the original row choices.
    Each target mode belongs to one packet. The global exponent test
    is the conjunction of the separate packet tests. -/
theorem packetCoeff_product
    (row : ∀ k, Rows k → Option (Modes k) → R) (β : ∀ k, Modes k → ℕ) :
    (∏ k, packetCoeff (row k) (β k)) =
      ∑ choices : (∀ k, Rows k → Option (Modes k)),
        if ∀ k z, Fintype.card {r // choices k r = some z} = β k z then
          ∏ k, ∏ r, row k r (choices k r)
        else 0 := by
  unfold packetCoeff
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro choices _
  by_cases h : ∀ k z, Fintype.card {r // choices k r = some z} = β k z
  · simp only [if_pos h, if_pos (h _)]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨k,z,hz⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg (fun h => hz (h z)))

/-- Append the source tile powers and multiply by the original group
    entries. This is the distributive step needed to relate packet entry
    computations to a whole group's coefficient sum. -/
theorem packetValue_product {Reads : P → Type*} [∀ k, Fintype (Reads k)]
    (row : ∀ k, Rows k → Option (Modes k) → R) (β : ∀ k, Modes k → ℕ)
    (tile : ∀ k, Reads k → R) (powers : ∀ k, Reads k → ℕ) (orig : R) :
    orig * (∏ k, packetValue (row k) (β k) (tile k) (powers k)) =
      ∑ choices : (∀ k, Rows k → Option (Modes k)),
        if ∀ k z, Fintype.card {r // choices k r = some z} = β k z then
          orig * (∏ k, ∏ r, row k r (choices k r)) * (∏ k, ∏ z, tile k z ^ powers k z)
        else 0 := by
  simp only [packetValue,Finset.prod_mul_distrib,← mul_assoc,packetCoeff_product,
    Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro choices _
  split <;> simp_all only [mul_zero, zero_mul]

#print axioms packetCoeff_product
#print axioms packetValue_product

end RootSeparation.Solver
