
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic

namespace NativeInterpolation
open scoped BigOperators Polynomial Matrix
open Polynomial

variable {R : Type*} [CommRing R] {d : ℕ}

/-- Decode the coefficients from probe samples in a commutative ring. -/
noncomputable def decode (x samples : Fin (d+1) → R) : Fin (d+1) → R :=
  (Matrix.vandermonde x)⁻¹ *ᵥ samples

theorem unit_prod {ι : Type*} (s : Finset ι) (g : ι → R)
    (h : ∀ j ∈ s, IsUnit (g j)) : IsUnit (∏ j ∈ s, g j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj]
    exact (h j (Finset.mem_insert_self _ _)).mul
      (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))

theorem det_isUnit (x : Fin (d+1) → R)
    (h : ∀ i j, i ≠ j → IsUnit (x j - x i)) :
    IsUnit (Matrix.vandermonde x).det := by
  rw [Matrix.det_vandermonde]
  apply unit_prod
  intro i _
  apply unit_prod
  intro j hj
  exact h i j (ne_of_lt (Finset.mem_Ioi.mp hj))

theorem decode_mulVec (x a : Fin (d+1) → R)
    (h : ∀ i j, i ≠ j → IsUnit (x j - x i)) :
    decode x (Matrix.vandermonde x *ᵥ a) = a := by
  rw [decode, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (det_isUnit x h),
    Matrix.one_mulVec]

theorem eval_eq_coeffVector (p : R[X]) (hp : p.natDegree ≤ d) (x : Fin (d+1) → R) :
    (fun i => p.eval (x i)) =
      Matrix.vandermonde x *ᵥ (fun j => p.coeff (j : ℕ)) := by
  funext i
  have he : p = ∑ j ∈ Finset.range (d+1), monomial j (p.coeff j) :=
    Polynomial.as_sum_range' p (d+1) (by omega)
  calc
    p.eval (x i) = (∑ j ∈ Finset.range (d+1), monomial j (p.coeff j)).eval (x i) :=
      congrArg (Polynomial.eval (x i)) he
    _ = ∑ j ∈ Finset.range (d+1), (x i)^j * p.coeff j := by
      simp only [Polynomial.eval_finset_sum, Polynomial.eval_monomial]
      apply Finset.sum_congr rfl
      intro _ _
      exact mul_comm _ _
    _ = _ := by
      rw [← Fin.sum_univ_eq_sum_range]
      rfl

/-- Unit-separated probes may omit zero. Rings may have zero divisors. -/
theorem decode_eval (p : R[X]) (hp : p.natDegree ≤ d) (x : Fin (d+1) → R)
    (h : ∀ i j, i ≠ j → IsUnit (x j - x i)) :
    decode x (fun i => p.eval (x i)) = fun j : Fin (d+1) => p.coeff (j : ℕ) := by
  rw [eval_eq_coeffVector p hp x, decode_mulVec x _ h]

/-- Finite expansion after passage to a ring with 2^prec = 0.
    Terms past this window cannot affect any integral probe. -/
noncomputable def normalized (prec v k : ℕ) (c : ℕ → R) : R[X] :=
  ∑ j ∈ Finset.range prec, C ((2 : R) ^ (v+j) * c j) * X ^ (k+j)

theorem normalized_degree (prec v k : ℕ) (c : ℕ → R)
    (h0 : (2 : R) ^ prec = 0) (hk : k ≤ v) :
    (normalized prec v k c).natDegree ≤ prec := by
  unfold normalized
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  by_cases h : k+j ≤ prec
  · apply Polynomial.natDegree_mul_le.trans
    simp only [Polynomial.natDegree_C, zero_add]
    apply Polynomial.natDegree_pow_le.trans
    exact (Nat.mul_le_mul_left _ Polynomial.natDegree_X_le).trans (by simpa using h)
  · have hz : (2 : R) ^ (v+j) = 0 := by
      have hf : v+j = prec + (v+j-prec) := by omega
      rw [hf, pow_add, h0, zero_mul]
    simp [hz]

theorem normalized_singleton_coeff (prec v : ℕ) (c : ℕ → R) (hp : 0 < prec) :
    (normalized prec v 1 c).coeff 1 = (2 : R) ^ v * c 0 := by
  unfold normalized
  rw [Polynomial.finset_sum_coeff, Finset.sum_eq_single 0]
  · simp only [Nat.add_zero, Polynomial.C_mul_X_pow_eq_monomial,
      Polynomial.coeff_monomial, if_true]
  · intro j _ hj
    rw [Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coeff_monomial]
    exact if_neg (by omega)
  · simp [hp]

/-- J8 readout over any finite-precision receiving ring at unit-separated probes. -/
theorem singleton_from_completed_probes (prec v : ℕ) (c : ℕ → R)
    (hp : 0 < prec) (hv : 1 ≤ v) (hnil : (2 : R) ^ prec = 0)
    (x : Fin (prec+1) → R) (h : ∀ i j, i ≠ j → IsUnit (x j - x i)) :
    decode x (fun i => (normalized prec v 1 c).eval (x i)) ⟨1,by omega⟩ =
      (2 : R) ^ v * c 0 := by
  rw [decode_eval _ (normalized_degree prec v 1 c hnil hv) x h]
  exact normalized_singleton_coeff prec v c hp

theorem normalized_eval (prec v k : ℕ) (c : ℕ → R) (z : R) :
    (normalized prec v k c).eval z =
      (2 : R) ^ v * z ^ k * ∑ j ∈ Finset.range prec, c j * ((2 : R) * z) ^ j := by
  simp only [normalized, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [pow_add (2 : R), pow_add z, mul_pow]
  ring

/-- A distinct residue image and the local-ring unit test certify a legal probe set. -/
theorem unit_differences_from_residue {K : Type*} [Field K] (res : R →+* K)
    (unitTest : ∀ a, res a ≠ 0 → IsUnit a) (x : Fin (d+1) → R)
    (hinj : Function.Injective (res ∘ x)) :
    ∀ i j, i ≠ j → IsUnit (x j - x i) := by
  intro i j hij
  apply unitTest
  rw [map_sub, sub_ne_zero]
  intro h
  exact hij (hinj h.symm)

/-- J8/J9 executable inverse after returning to the base residue.
    An extension-valued residue may be projected by any left inverse to the
    known base-ring embedding (e.g. its constant coordinate). -/
theorem lift_exact_after_interpolation {O : Type*} [CommRing O] (prec v : ℕ)
    (hp : 0 < prec) (hv : 1 ≤ v) (hnil : (2 : O)^prec = 0)
    (c : ℕ → O) (x : Fin (prec+1) → O) (hu : ∀ i j, i ≠ j → IsUnit (x j - x i))
    (embed : ZMod (2^prec) →+* O) (project : O → ZMod (2^prec))
    (left : Function.LeftInverse project embed) (D a : ℤ)
    (fits : a * 2 ∈ Set.Ioc (-(↑((2:ℕ)^prec)) : ℤ) ↑((2:ℕ)^prec))
    (lifted : (D : O) * ((2 : O)^v * c 0) = embed (a : ZMod (2^prec))) :
    (project ((D : O) * decode x (fun i => (normalized prec v 1 c).eval (x i))
      ⟨1,by omega⟩)).valMinAbs = a := by
  haveI : NeZero ((2 : ℕ)^prec) := ⟨pow_ne_zero _ (by decide)⟩
  rw [singleton_from_completed_probes prec v c hp hv hnil x hu, lifted, left]
  exact (ZMod.valMinAbs_spec _ _).mpr ⟨rfl, fits⟩

theorem lift_rational_after_interpolation {O : Type*} [CommRing O] (prec v : ℕ)
    (hp : 0 < prec) (hv : 1 ≤ v) (hnil : (2 : O)^prec = 0)
    (c : ℕ → O) (x : Fin (prec+1) → O) (hu : ∀ i j, i ≠ j → IsUnit (x j - x i))
    (embed : ZMod (2^prec) →+* O) (project : O → ZMod (2^prec))
    (left : Function.LeftInverse project embed) (D a : ℤ) (hd : D ≠ 0) (y : ℚ)
    (fits : a * 2 ∈ Set.Ioc (-(↑((2:ℕ)^prec)) : ℤ) ↑((2:ℕ)^prec))
    (lifted : (D : O) * ((2 : O)^v * c 0) = embed (a : ZMod (2^prec)))
    (numerator : (a : ℚ) = D * y) :
    ((project ((D : O) * decode x (fun i => (normalized prec v 1 c).eval (x i))
      ⟨1,by omega⟩)).valMinAbs : ℚ) / D = y := by
  rw [lift_exact_after_interpolation prec v hp hv hnil c x hu embed project left D a fits lifted,
    numerator]
  exact mul_div_cancel_left₀ y (by exact_mod_cast hd)

#print axioms lift_exact_after_interpolation
#print axioms lift_rational_after_interpolation

#print axioms normalized_eval
#print axioms unit_differences_from_residue

#print axioms det_isUnit
#print axioms decode_eval
#print axioms normalized_degree
#print axioms normalized_singleton_coeff
#print axioms singleton_from_completed_probes
end NativeInterpolation

