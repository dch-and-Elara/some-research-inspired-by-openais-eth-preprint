import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Fixed linear finite-receiver decoding on separately lifted children.
The residue section is used only pointwise; it is never additive. -/
namespace Paper5.D1Literal
open scoped BigOperators

noncomputable def probeBasis {B Z : Type*} [Zero B] [One B] (z : Z) : Z → B := by
  classical
  exact fun x => if x=z then 1 else 0

theorem linear_on_probe_basis {B Z J : Type*} [CommRing B] [Fintype Z]
    (D : (Z → B) →ₗ[B] (J → B)) (b : Z → B) (j : J) :
    D b j = ∑ z : Z, D (probeBasis z) j * b z := by
  classical
  have hr : (∑ z : Z, b z • (probeBasis z : Z → B)) = b := by
    funext i
    simp [probeBasis, Pi.smul_apply, smul_eq_mul, mul_ite]
  conv_lhs => rw [← hr]
  rw [map_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

section Lift
variable {A B Z J : Type*} [CommRing A] [CommRing B] [Fintype Z]

noncomputable def liftedCoefficient
    (D : (Z → B) →ₗ[B] (J → B)) (lift : B → A) (s : Z → A) (j : J) : A :=
  ∑ z, lift (D (probeBasis z) j) * s z

theorem reduce_liftedCoefficient (D : (Z → B) →ₗ[B] (J → B))
    (reduce : A →+* B) (lift : B → A) (hlift : ∀ b, reduce (lift b) = b)
    (s : Z → A) (j : J) :
    reduce (liftedCoefficient D lift s j) = D (fun z => reduce (s z)) j := by
  rw [linear_on_probe_basis D]
  simp only [liftedCoefficient, map_sum, map_mul, hlift]

variable {M G : Type*} [Fintype M] [Fintype G]

def liftedChildSum (lift : B → A) (child : M → G → B) : A :=
  ∑ m, ∏ g, lift (child m g)

theorem reduce_liftedChildSum (reduce : A →+* B) (lift : B → A)
    (hlift : ∀ b, reduce (lift b) = b) (child : M → G → B) :
    reduce (liftedChildSum lift child) = ∑ m, ∏ g, child m g := by
  simp only [liftedChildSum, map_sum, map_prod, hlift]

theorem reduce_liftedChild_decode (D : (Z → B) →ₗ[B] (J → B))
    (reduce : A →+* B) (lift : B → A) (hlift : ∀ b, reduce (lift b) = b)
    (child : Z → M → G → B) (j : J) :
    reduce (liftedCoefficient D lift (fun z => liftedChildSum lift (child z)) j) =
      D (fun z => ∑ m, ∏ g, child z m g) j := by
  rw [reduce_liftedCoefficient D reduce lift hlift]
  simp only [reduce_liftedChildSum reduce lift hlift]

/-- This coefficient may differ from a lift selected after decoding.
It has the same *residue*, which is the exact divisibility needed. -/
theorem lift_errors_relative_to_true (D : (Z → B) →ₗ[B] (J → B))
    (reduce : A →+* B) (lift : B → A) (hlift : ∀ b, reduce (lift b) = b)
    (p : ℕ) (kernel : ∀ x, reduce x = 0 ↔ (2:A)^p ∣ x)
    (child : Z → M → G → B) (truth : J → A)
    (correct : ∀ j, D (fun z => ∑ m, ∏ g, child z m g) j = reduce (truth j)) :
    ∀ j, (2:A)^p ∣ liftedCoefficient D lift (fun z => liftedChildSum lift (child z)) j - truth j := by
  intro j
  apply (kernel _).mp
  rw [map_sub, reduce_liftedChild_decode D reduce lift hlift, correct, sub_self]

section FieldExpression
variable {K : Type*} [CommRing K] [Fintype J]

noncomputable def publicWeight (D : (Z → B) →ₗ[B] (J → B))
    (lift : B → A) (embed : A →+* K) (w : J → K) (z : Z) : K :=
  ∑ j, w j * embed (lift (D (probeBasis z) j))

/-- Exactly one field summand per native (probe, mode) address, not
per (probe, mode, retained coefficient). -/
theorem one_term_per_native_slot (D : (Z → B) →ₗ[B] (J → B))
    (lift : B → A) (embed : A →+* K) (w : J → K) (child : Z → M → G → B) :
    (∑ j, w j * embed (liftedCoefficient D lift (fun z => liftedChildSum lift (child z)) j)) =
      ∑ z, ∑ m, publicWeight D lift embed w z * ∏ g, embed (lift (child z m g)) := by
  classical
  calc
    _ = ∑ j, ∑ z, (w j * embed (lift (D (probeBasis z) j))) *
          embed (liftedChildSum lift (child z)) := by
      simp only [liftedCoefficient, map_sum, map_mul, Finset.mul_sum, mul_assoc]
    _ = ∑ z, ∑ j, (w j * embed (lift (D (probeBasis z) j))) *
          embed (liftedChildSum lift (child z)) := Finset.sum_comm
    _ = ∑ z, publicWeight D lift embed w z * embed (liftedChildSum lift (child z)) := by
      simp only [publicWeight, Finset.sum_mul]
    _ = _ := by
      simp only [liftedChildSum, map_sum, map_prod, Finset.mul_sum]

end FieldExpression
end Lift

#print axioms linear_on_probe_basis
#print axioms reduce_liftedCoefficient
#print axioms reduce_liftedChildSum
#print axioms reduce_liftedChild_decode
#print axioms lift_errors_relative_to_true
#print axioms one_term_per_native_slot
end Paper5.D1Literal

