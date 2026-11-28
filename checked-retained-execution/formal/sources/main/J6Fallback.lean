import J6Mesh
import NativeInterpolation
import Mathlib.Tactic

/-! J6 when the prescribed probe set omits zero. The global degree bound
comes from the product of the per-wire kernels. Constant coefficient
readout needs only these same zero-mode addresses, not any other mode. -/
namespace J6Fallback
open scoped Polynomial BigOperators
variable {O P Y X : Type*} [CommRing O] [Fintype P] [Fintype Y] [Fintype X]

noncomputable def zeroModePolynomial (A : Y → O) (B : X → O)
    (wire : P → Y → X → O[X]) : O[X] :=
  ∑ y : Y, ∑ x : X, Polynomial.C (A y * B x) * ∏ p : P, wire p y x

theorem zeroMode_degree (A : Y → O) (B : X → O) (wire : P → Y → X → O[X])
    (L : ℕ) (h : ∀ p y x, (wire p y x).natDegree ≤ 2*L-1) :
    (zeroModePolynomial A B wire).natDegree ≤ Fintype.card P*(2*L-1) := by
  unfold zeroModePolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro y hy
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x hx
  apply Polynomial.natDegree_mul_le.trans
  simp only [Polynomial.natDegree_C,zero_add]
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _p : P, (2*L-1) := Finset.sum_le_sum (fun p _ => h p y x)
    _ = _ := by simp

theorem recover_zero_slot (m : ℕ) (A : Y → O) (B : X → O)
    (wire : P → Y → X → O[X]) (hP : Fintype.card P = J6Mesh.M m)
    (h : ∀ p y x, (wire p y x).natDegree ≤ 2*J6Mesh.L m-1)
    (grid : Fin (J6Mesh.M m*(2*J6Mesh.L m-1)+1) → O)
    (hu : ∀ i j, i ≠ j → IsUnit (grid j-grid i)) :
    NativeInterpolation.decode grid (fun i => (zeroModePolynomial A B wire).eval (grid i))
      ⟨0,by omega⟩ = (zeroModePolynomial A B wire).eval 0 := by
  have hd := zeroMode_degree A B wire (J6Mesh.L m) h
  rw [hP] at hd
  rw [NativeInterpolation.decode_eval _ hd grid hu]
  exact Polynomial.coeff_zero_eq_eval_zero _

#print axioms zeroMode_degree
#print axioms recover_zero_slot
end J6Fallback
