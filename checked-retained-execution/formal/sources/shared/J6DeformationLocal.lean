import J6DeformationPoly
import J6R9PacketLocal
import Mathlib.Algebra.Polynomial.Roots

namespace J6DeformationLocal
open scoped Classical BigOperators Polynomial
open P1DyadicGrid Polynomial J6DeformationPoly
open DenominatorBudget

noncomputable def coordinate (a : ℕ) (t : ℤ) : ℚ[X] :=
  C (t:ℚ) + C ((2:ℚ)^(a+1)) * X

theorem entry_eval (a : ℕ) (k : ℤ) (T : ℚ) :
    (entry ℚ a k).eval T = J6R9PacketLocal.printedW a k T := by
  simp [entry,J6R9PacketLocal.printedW,eval_prod,eval_sub,div_eq_mul_inv,mul_comm]

/-- The rational global entry and the integral local entry are literally
the same polynomial after the printed affine coordinate change. -/
theorem entry_local_map {a : ℕ} {t k : ℤ} (ht : t ∈ grid a) (hk : k ∈ grid a) :
    (entry ℚ a k).comp (coordinate a t) =
      (J6R9PacketLocal.W a t k).map twoLocalRat := by
  apply Polynomial.eq_of_infinite_eval_eq
  have h : {z : ℚ | ((entry ℚ a k).comp (coordinate a t)).eval z =
      ((J6R9PacketLocal.W a t k).map twoLocalRat).eval z} = Set.univ := by
    ext z
    simp only [Set.mem_setOf_eq,Set.mem_univ, iff_true, eval_comp, coordinate,
      eval_add, eval_mul, eval_C, eval_X, entry_eval, eval_map]
    exact (J6R9PacketLocal.W_eval_rat ht hk z).symm
  rw [h]
  exact Set.infinite_univ

#print axioms entry_eval
#print axioms entry_local_map
end J6DeformationLocal
