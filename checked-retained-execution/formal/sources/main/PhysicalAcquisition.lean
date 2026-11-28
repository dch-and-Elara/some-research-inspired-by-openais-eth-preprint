import ShiftedAcquisition
import Mathlib.Algebra.Ring.Parity

/-! The finite signed partition identity behind the one-point sparse-CNF
edge-cover reduction. Graph placement and the bound making a modular
representative exact are separate source-level arguments. -/

set_option autoImplicit false
set_option warningAsError true

namespace PhysicalAcquisition

open scoped BigOperators
open ShiftedAcquisition

variable {R : Type*} [CommRing R]

theorem affine_mass (a : R) : (∑ b : Bool, affine b a) = 1 := by
  simp [affine]

theorem affine_moment (a : R) : (∑ b : Bool, spin b * affine b a) = a := by
  simp [affine, spin]

/-- Sum the old all-negative physical clause table against all incident affine kernels. -/
theorem negative_row {I : Type*} [Fintype I] [DecidableEq I] (a : I → R) :
    (∑ y : I → Bool, (1 - ∏ i : I, (spin (y i) : R)) * ∏ i : I, affine (y i) (a i)) =
      1 - ∏ i : I, a i := by
  simp_rw [sub_mul, one_mul]
  rw [Finset.sum_sub_distrib, ← Fintype.prod_sum (fun i (b : Bool) => affine b (a i))]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : Bool) => (spin b : R) * affine b (a i))]
  simp only [affine_mass, affine_moment, Finset.prod_const_one]

theorem even_negative_row {I : Type*} [Fintype I] [DecidableEq I]
    (h : Even (Fintype.card I)) (x : I → Bool) :
    (∑ y : I → Bool, (1 - ∏ i : I, (spin (y i) : R)) *
      ∏ i : I, shiftMatrix (R := R) (y i) (x i)) = 1 - ∏ i : I, (spin (x i) : R) := by
  simp_rw [matrix_is_affine]
  rw [negative_row, Finset.prod_neg]
  simp [h.neg_one_pow]

/-- Each unary pin contributes a sign and forces a one, regardless of any
dependence of the other factors on its bit. -/
theorem signed_pins {A : Type*} [Fintype A] [DecidableEq A] (f : (A → Bool) → R) :
    (∑ z : A → Bool, f z * ∏ i : A, -(spin (z i) : R)) =
      f (fun _ => true) * (-1 : R) ^ (Fintype.card A) := by
  classical
  rw [Finset.sum_eq_single (fun _ : A => true)]
  · simp [spin]
  · intro z _ hz
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ true := Function.ne_iff.mp hz
    have hz0 : (∏ a : A, -(spin (z a) : R)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [spin, hi])
    simp [hz0]
  · simp

/-- Summing every non-designated equality bit independently. -/
theorem other_columns {C : Type*} [Fintype C] [DecidableEq C] (d : C → ℕ) :
    (∑ q : C → Bool, ∏ c : C, (1 + (spin (q c) : R)) ^ d c) =
      ∏ c : C, (1 + (2 : R) ^ d c) := by
  rw [← Fintype.prod_sum (fun c (b : Bool) => (1 + (spin b : R)) ^ d c)]
  apply Finset.prod_congr rfl
  intro c _
  simp [spin, add_comm, one_add_one_eq_two]

def covers {V E : Type*} (inc : V → Finset E) (x : E → Bool) : Prop :=
  ∀ v, ∃ e ∈ inc v, x e = false

theorem one_vertex {E : Type*} (edges : Finset E) (x : E → Bool) :
    (1 - ∏ e ∈ edges, (spin (x e) : R)) =
    (if ∃ e ∈ edges, x e = false then 1 else 0) := by
  classical
  by_cases h : ∃ e ∈ edges, x e = false
  · obtain ⟨e, he, hx⟩ := h
    have hz : (∏ j ∈ edges, (spin (x j) : R)) = 0 :=
      Finset.prod_eq_zero he (by simp [spin, hx])
    simp [hz, show ∃ e ∈ edges, x e = false from ⟨e, he, hx⟩]
  · have ho : (∏ e ∈ edges, (spin (x e) : R)) = 1 := by
      apply Finset.prod_eq_one
      intro e he
      cases hx : x e
      · exact False.elim (h ⟨e, he, hx⟩)
      · simp [spin]
    simp [ho, h]

theorem cover_factors {V E : Type*} [Fintype V] (inc : V → Finset E) (x : E → Bool)
    [Decidable (covers inc x)] :
    (∏ v : V, (1 - ∏ e ∈ inc v, (spin (x e) : R))) = if covers inc x then 1 else 0 := by
  classical
  simp_rw [one_vertex]
  by_cases h : covers inc x
  · simp [h, show ∀ v, ∃ e ∈ inc v, x e = false from h]
  · rw [if_neg h]
    obtain ⟨v, hv⟩ : ∃ v, ¬ ∃ e ∈ inc v, x e = false := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])

def controlValue {A : Type*} (z : A → Bool) : Option A → R
  | none => 1
  | some i => spin (z i)

theorem control_true {A : Type*} (a : Option A) :
    controlValue (R := R) (fun _ => true) a = 1 := by cases a <;> simp [controlValue, spin]

/-- The finite normalization in (A6). Zeros of x describe covered edges.
The optional control at a vertex is pinned to one by an actual signed sum.
Even many unary controls cancel their global sign. -/
theorem physical_normalization {V E A C : Type*} [Fintype V] [Fintype E] [DecidableEq E]
    [Fintype A] [DecidableEq A] [Fintype C] [DecidableEq C] (inc : V → Finset E)
    [DecidablePred (covers inc)] (ctl : V → Option A) (d : C → ℕ)
    (heven : Even (Fintype.card A)) :
    (∑ x : E → Bool, ∑ z : A → Bool, ∑ q : C → Bool,
        (∏ v : V, (1 - (∏ e ∈ inc v, (spin (x e) : R)) * controlValue z (ctl v))) *
        (∏ i : A, -(spin (z i) : R)) * ∏ c : C, (1 + (spin (q c) : R)) ^ d c) =
      ((Finset.univ.filter (covers inc)).card : R) * ∏ c : C, (1 + (2 : R) ^ d c) := by
  classical
  let rows (x : E → Bool) (z : A → Bool) : R :=
    ∏ v : V, (1 - (∏ e ∈ inc v, (spin (x e) : R)) * controlValue z (ctl v))
  change (∑ x : E → Bool, ∑ z : A → Bool, ∑ q : C → Bool,
    (rows x z * ∏ i : A, -(spin (z i) : R)) * ∏ c : C, (1 + (spin (q c) : R)) ^ d c) = _
  simp_rw [← Finset.mul_sum, other_columns, ← Finset.sum_mul, signed_pins, heven.neg_one_pow,
    mul_one, rows, control_true, mul_one, cover_factors]
  rw [Finset.sum_boole]

#print axioms affine_mass
#print axioms affine_moment
#print axioms negative_row
#print axioms even_negative_row
#print axioms signed_pins
#print axioms other_columns
#print axioms one_vertex
#print axioms cover_factors
#print axioms control_true
#print axioms physical_normalization

end PhysicalAcquisition
