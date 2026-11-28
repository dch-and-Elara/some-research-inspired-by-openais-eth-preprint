import LayerRecovery

/-! The boundary-layer factors in J6. The unmatched old rows have no
incoming shift and are forced to the zero word by the contraction;
the unmatched columns are independent binary subdivision equalities. -/
namespace J6BoundaryFactors
open scoped BigOperators Polynomial
open Polynomial

theorem no_read_singleton {P : Type*} [Fintype P] [DecidableEq P]
    (A : (P → Bool) → ℚ) (c : ℚ) :
    (∑ y : P → Bool, A y *
      ∏ j, (LayerRecovery.wireFactor (y j) false).eval c) = A (fun _ => false) := by
  classical
  rw [Finset.sum_eq_single (fun _ => false)]
  · simp [LayerRecovery.wireFactor]
  · intro y _ hy
    have hw : ∃ j, y j = true := by
      by_contra! h
      apply hy
      funext j
      cases hh : y j <;> simp_all
    obtain ⟨j,hj⟩ := hw
    have hp : (∏ j, (LayerRecovery.wireFactor (y j) false).eval c) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [hj,LayerRecovery.wireFactor]
    rw [hp,mul_zero]
  · simp

theorem free_subdivisions {Q : Type*} [Fintype Q] [DecidableEq Q] :
    (∑ x : Q × Bool → Bool,
      if ∀ j : Q, x (j,false) = x (j,true) then (1:ℚ) else 0) = 2^Fintype.card Q := by
  classical
  let f : (Q → Bool) ≃ {x : Q × Bool → Bool // ∀ j : Q, x (j,false) = x (j,true)} :=
    { toFun := fun x => ⟨fun j => x j.1, fun _ => rfl⟩
      invFun := fun x j => x.1 (j,false)
      left_inv := fun _ => rfl
      right_inv := by
        intro x
        apply Subtype.ext
        funext j
        obtain ⟨j,b⟩ := j
        cases b
        · rfl
        · exact x.2 j }
  have hc : Fintype.card {x : Q × Bool → Bool // ∀ j : Q, x (j,false) = x (j,true)} =
      2^Fintype.card Q := by
    rw [← Fintype.card_congr f]
    simp
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast (Fintype.card_subtype (p := fun x : Q × Bool → Bool =>
    ∀ j : Q, x (j,false) = x (j,true))).symm.trans hc

#print axioms no_read_singleton
#print axioms free_subdivisions
end J6BoundaryFactors