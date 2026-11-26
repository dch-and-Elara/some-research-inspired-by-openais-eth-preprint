import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Span.Basic

/-!
# Exact transport of independent coordinate errors

The possible input perturbations have independently varying coefficients in the
base ring. A linear decoder sends their full lattice to the span of its scaled
columns. A field-valued matrix may have nonintegral entries. Its precision test
is membership in an explicit base-ring lattice, or, for given numerator and
denominator representations, a divisibility test entirely in the base ring.
These statements apply to any fixed linear decoder. They do not construct
denominators for a particular interpolation or readout formula.
-/

namespace PrecisionLattice

open scoped BigOperators

variable {R J : Type*} [CommRing R]

section LinearCombinations

variable {V : Type*} [AddCommGroup V] [Module R V] [Fintype J]

/-- With independent coefficients, containment of every perturbation is
equivalent to containment of each generator. The forward implication tests
the individual unit vectors. -/
theorem all_combinations_mem_iff (g : J → V) (T : Submodule R V) :
    (∀ e : J → R, (∑ j, e j • g j) ∈ T) ↔ ∀ j, g j ∈ T := by
  classical
  constructor
  · intro h j
    simpa [ite_smul] using h (fun k => if k = j then 1 else 0)
  · intro h e
    exact T.sum_mem fun j _ => T.smul_mem (e j) (h j)

end LinearCombinations

section InputLattice

/-- Scaling the independent uncertainty coefficients by their coordinate generators. -/
def coordinateScale (a : J → R) : (J → R) →ₗ[R] (J → R) where
  toFun e j := a j * e j
  map_add' e f := funext fun j => mul_add (a j) (e j) (f j)
  map_smul' r e := funext fun j => mul_left_comm (a j) r (e j)

/-- The actual set of attainable input perturbations, as a submodule. -/
def coordinateLattice (a : J → R) : Submodule R (J → R) :=
  LinearMap.range (coordinateScale a)

theorem mem_coordinateLattice_iff (a x : J → R) :
    x ∈ coordinateLattice a ↔ ∀ j, a j ∣ x j := by
  constructor
  · rintro ⟨e, rfl⟩ j
    exact ⟨e j, rfl⟩
  · intro h
    choose e he using h
    exact ⟨e, funext fun j => (he j).symm⟩

variable [Fintype J] [DecidableEq J]
variable {V : Type*} [AddCommGroup V] [Module R V]

/-- The coordinate vector is a sum of individually scaled unit-coordinate vectors. -/
theorem coordinateScale_eq_sum (a e : J → R) :
    coordinateScale a e = ∑ j, e j • (Pi.single j (a j) : J → R) := by
  calc
    coordinateScale a e = ∑ j, Pi.single j (coordinateScale a e j) :=
      (Finset.univ_sum_single _).symm
    _ = ∑ j, e j • (Pi.single j (a j) : J → R) := by
      apply Finset.sum_congr rfl
      intro j _
      change (Pi.single j (a j * e j) : J → R) = e j • (Pi.single j (a j) : J → R)
      rw [mul_comm]
      exact Pi.single_smul' j (e j) (a j)

/-- Exact decoder precision, quantified over actual independent input errors. -/
theorem decoder_precision_iff (D : (J → R) →ₗ[R] V) (a : J → R) (T : Submodule R V) :
    (∀ e : J → R, D (coordinateScale a e) ∈ T) ↔
      ∀ j, D (Pi.single j (a j)) ∈ T := by
  simpa only [coordinateScale_eq_sum, map_sum, map_smul] using
    (all_combinations_mem_iff (fun j => D (Pi.single j (a j))) T)

/-- Containment of the transported input lattice has the same exact column test. -/
theorem decoder_map_le_iff (D : (J → R) →ₗ[R] V) (a : J → R) (T : Submodule R V) :
    (coordinateLattice a).map D ≤ T ↔ ∀ j, D (Pi.single j (a j)) ∈ T := by
  rw [← decoder_precision_iff]
  constructor
  · intro h e
    exact h ⟨coordinateScale a e, ⟨e, rfl⟩, rfl⟩
  · rintro h _ ⟨_, ⟨e, rfl⟩, rfl⟩
    exact h e

/-- The complete transported error lattice, including output correlations. -/
theorem decoder_map_eq_span_columns (D : (J → R) →ₗ[R] V) (a : J → R) :
    (coordinateLattice a).map D =
      Submodule.span R (Set.range fun j => D (Pi.single j (a j))) := by
  apply le_antisymm
  · exact (decoder_map_le_iff D a _).2 fun j => Submodule.subset_span ⟨j, rfl⟩
  · apply Submodule.span_le.2
    rintro _ ⟨j, rfl⟩
    exact (decoder_map_le_iff D a _).1 le_rfl j

end InputLattice

section FieldMatrix

variable {K I : Type*} [Field K] [Algebra R K]

/-- The base-ring multiples of an embedded element, viewed inside the field. -/
def integralMultiples (K : Type*) [Field K] [Algebra R K] (b : R) : Submodule R K :=
  Submodule.span R {algebraMap R K b}

theorem mem_integralMultiples_iff (b : R) (x : K) :
    x ∈ integralMultiples K b ↔ ∃ u : R, x = algebraMap R K (b * u) := by
  rw [integralMultiples, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, by rw [Algebra.smul_def, map_mul, mul_comm]⟩
  · rintro ⟨u, rfl⟩
    exact ⟨u, by rw [Algebra.smul_def, map_mul, mul_comm]⟩

variable [Fintype J]

/-- Apply the actual field coefficients to the embedded, scaled errors. -/
def matrixError (C : I → J → K) (a e : J → R) (i : I) : K :=
  ∑ j, C i j * (algebraMap R K (a j) * algebraMap R K (e j))

theorem matrixError_eq_smul_sum (C : I → J → K) (a e : J → R) (i : I) :
    matrixError C a e i = ∑ j, e j • (C i j * algebraMap R K (a j)) := by
  apply Finset.sum_congr rfl
  intro j _
  rw [Algebra.smul_def]
  ac_rfl

/-- Exact simultaneous entrywise precision. Each witness lies in the base
ring, even when the entries of the transfer matrix lie only in the field. -/
theorem matrix_precision_iff (C : I → J → K) (a : J → R) (b : I → R) :
    (∀ (e : J → R) (i : I), ∃ u : R, matrixError C a e i = algebraMap R K (b i * u)) ↔
      ∀ i j, ∃ u : R, C i j * algebraMap R K (a j) = algebraMap R K (b i * u) := by
  have hrow (i : I) :
      (∀ e : J → R, ∃ u : R, matrixError C a e i = algebraMap R K (b i * u)) ↔
        ∀ j, ∃ u : R, C i j * algebraMap R K (a j) = algebraMap R K (b i * u) := by
    simp_rw [matrixError_eq_smul_sum, ← mem_integralMultiples_iff]
    exact all_combinations_mem_iff _ _
  exact ⟨fun h i => (hrow i).1 (fun e => h e i), fun h e i => (hrow i).2 (h i) e⟩

/-- Precision powers may vary independently across the inputs and the outputs. -/
theorem matrix_power_precision_iff (C : I → J → K) (π : R) (P : J → ℕ) (p : I → ℕ) :
    (∀ (e : J → R) (i : I), ∃ u : R,
      matrixError C (fun j => π ^ P j) e i = algebraMap R K (π ^ p i * u)) ↔
      ∀ i j, ∃ u : R, C i j * algebraMap R K (π ^ P j) = algebraMap R K (π ^ p i * u) :=
  matrix_precision_iff C (fun j => π ^ P j) (fun i => π ^ p i)

/-- Clearing one specified nonzero denominator. The representing identity
for the field element makes no integrality assumption on that element. -/
theorem column_clear_denominator_iff (hinj : Function.Injective (algebraMap R K))
    (c : K) (a b n d : R) (hd : algebraMap R K d ≠ 0)
    (hrep : c * algebraMap R K d = algebraMap R K n) :
    (∃ u : R, c * algebraMap R K a = algebraMap R K (b * u)) ↔ d * b ∣ n * a := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, hinj ?_⟩
    calc
      algebraMap R K (n * a) = (c * algebraMap R K d) * algebraMap R K a := by
        rw [map_mul, hrep]
      _ = algebraMap R K d * (c * algebraMap R K a) := by ac_rfl
      _ = algebraMap R K ((d * b) * u) := by simp only [hu, mul_assoc, map_mul]
  · rintro ⟨u, hu⟩
    refine ⟨u, mul_right_cancel₀ hd ?_⟩
    calc
      (c * algebraMap R K a) * algebraMap R K d =
          (c * algebraMap R K d) * algebraMap R K a := by ac_rfl
      _ = algebraMap R K (n * a) := by rw [hrep, map_mul]
      _ = algebraMap R K ((b * u) * d) := by rw [hu, mul_assoc, mul_comm d]
      _ = algebraMap R K (b * u) * algebraMap R K d := map_mul _ _ _

/-- The exact power-precision test expressed by divisibility in the base ring
for numerator and denominator data representing the fixed field coefficients. -/
theorem matrix_power_precision_clear_denominators_iff
    (hinj : Function.Injective (algebraMap R K))
    (C : I → J → K) (n d : I → J → R)
    (hd : ∀ i j, algebraMap R K (d i j) ≠ 0)
    (hrep : ∀ i j, C i j * algebraMap R K (d i j) = algebraMap R K (n i j))
    (π : R) (P : J → ℕ) (p : I → ℕ) :
    (∀ (e : J → R) (i : I), ∃ u : R,
      matrixError C (fun j => π ^ P j) e i = algebraMap R K (π ^ p i * u)) ↔
      ∀ i j, d i j * π ^ p i ∣ n i j * π ^ P j := by
  rw [matrix_power_precision_iff]
  exact forall_congr' fun i => forall_congr' fun j =>
    column_clear_denominator_iff hinj (C i j) _ _ _ _ (hd i j) (hrep i j)

end FieldMatrix

#print axioms all_combinations_mem_iff
#print axioms mem_coordinateLattice_iff
#print axioms decoder_precision_iff
#print axioms decoder_map_le_iff
#print axioms decoder_map_eq_span_columns
#print axioms matrix_precision_iff
#print axioms matrix_power_precision_iff
#print axioms column_clear_denominator_iff
#print axioms matrix_power_precision_clear_denominators_iff

end PrecisionLattice
