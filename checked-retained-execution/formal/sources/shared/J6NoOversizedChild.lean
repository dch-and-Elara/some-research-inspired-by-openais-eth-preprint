import J6PacketFold

namespace J6NoOversizedChild
open scoped Classical BigOperators
open MvPolynomial J6PacketCoefficientBridge J6LiteralCoeff J6ProfileMenu
variable {R M P G K : Type*} [CommRing R] [Fintype M] [DecidableEq M]
  [Fintype P] [Fintype K] [Fintype G] [DecidableEq G] [DecidableEq K]
  {U : G → Type*} [∀ g, Fintype (U g)]

omit [DecidableEq M] in
theorem oversized_child_product_zero (target source : M → G × K)
    (ports : G → K → Finset P) (retained : ∀ g, U g → R)
    (bit : ∀ g, U g → P → Bool) (base : ∀ g, U g → P → R)
    (cross : ∀ g, U g → P → M → R) (moment : ∀ g, U g → M → R)
    (beta : M →₀ ℕ) (h : ∃ m, Fintype.card P < beta m) :
    (∏ g, J6RecursiveModes.child target source ports retained bit base cross moment beta g) = 0 := by
  classical
  obtain ⟨m, hm⟩ := h
  let g := (target m).1
  let k := (target m).2
  apply Finset.prod_eq_zero (Finset.mem_univ g)
  unfold J6RecursiveModes.child
  refine Finset.sum_eq_zero (fun y _ => ?_)
  have hz : J6RecursiveModes.packet target source g k (ports g k)
      (bit g y) (base g y) (cross g y) (moment g y) beta = 0 := by
    unfold J6RecursiveModes.packet
    simp_rw [← source_signed_row]
    have hc : (ports g k).card < (beta.filter (fun j => target j = (g,k))) m := by
      have he : target m = (g,k) := Prod.eta _
      simp [he]
      exact (Finset.card_le_univ _).trans_lt hm
    rw [too_many_target_rows _ _ _ m hc, zero_mul]
  rw [Finset.prod_eq_zero (Finset.mem_univ k) hz, mul_zero]

#print axioms oversized_child_product_zero
end J6NoOversizedChild
