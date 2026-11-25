import ResearchCertificates
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Powerset

/-!
Further finite algebraic verification for unrestricted reconstruction.
No symmetry assumption is imposed on the measurement matrix.
-/

open scoped BigOperators
open Polynomial

namespace Reconstruction
noncomputable section

variable {V I M : Type*} [Fintype V] [Fintype I] [Fintype M] [DecidableEq V]

/-- Below half the remaining interpolation degree, the entire auxiliary
polynomial kernel vanishes, not just its constant term. -/
theorem auxiliary_kernel_zero
    (C : M → V → ℚ) (P : V → V → ℚ[X]) (t : I → ℚ)
    (slice : I → V → Prop) (h : V → ℚ[X]) (d k : ℕ)
    (ht : Function.Injective t) (ht0 : ∀ i, t i ≠ 0)
    (hP0 : ∀ u v, (P u v).eval 0 = if u = v then 1 else 0)
    (hloc : Locality C P t slice)
    (hker : ∀ a, (∑ v, Polynomial.C (C a v) * h v) = 0)
    (hsupp : ∀ i v, ¬slice i v → (h v).eval (t i) = 0)
    (hPd : ∀ u v, (P u v).natDegree ≤ d)
    (hhd : ∀ v, (h v).natDegree ≤ k)
    (hdeg : d + 2 * k < Fintype.card I) :
    ∀ v, h v = 0 := by
  classical
  induction k generalizing h with
  | zero =>
      have hz := square_certificate C P t slice h d 0 ht hP0 hloc
        hker hsupp hPd hhd hdeg
      intro v
      have hc : (h v).coeff 0 = 0 := by simpa only [Polynomial.coeff_zero_eq_eval_zero] using hz v
      rw [Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero (hhd v)), hc]
      exact Polynomial.C_0
  | succ k ih =>
      have hz := square_certificate C P t slice h d (k+1) ht hP0 hloc
        hker hsupp hPd hhd hdeg
      have hc : ∀ v, (h v).coeff 0 = 0 := by
        intro v
        simpa only [Polynomial.coeff_zero_eq_eval_zero] using hz v
      have hk' : ∀ a, (∑ v, Polynomial.C (C a v) * (h v).divX) = 0 := by
        intro a
        have he := congrArg Polynomial.divX_hom (hker a)
        simpa only [map_sum, Polynomial.divX_hom_toFun,
          Polynomial.divX_C_mul, Polynomial.divX_zero] using he
      have hs' : ∀ i v, ¬slice i v → ((h v).divX).eval (t i) = 0 := by
        intro i v hv
        have he := congrArg (fun f : ℚ[X] => f.eval (t i))
          (Polynomial.X_mul_divX_add (h v))
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
          Polynomial.eval_C, hc v, add_zero, hsupp i v hv] at he
        exact (mul_eq_zero.mp he).resolve_left (ht0 i)
      have hd' : ∀ v, ((h v).divX).natDegree ≤ k := by
        intro v
        rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one]
        have := hhd v
        omega
      have hi := ih (fun v => (h v).divX) hk' hs' hd' (by omega)
      dsimp only at hi
      intro v
      have he := Polynomial.X_mul_divX_add (h v)
      rw [hi v, hc v] at he
      simpa only [mul_zero, Polynomial.C_0, add_zero] using he.symm

#print axioms auxiliary_kernel_zero

def vectorPoly {n : ℕ} (a : Fin n → ℚ) : ℚ[X] :=
  ∑ i : Fin n, Polynomial.monomial (i : ℕ) (a i)

theorem vectorPoly_add {n : ℕ} (a b : Fin n → ℚ) :
    vectorPoly (a+b) = vectorPoly a + vectorPoly b := by
  simp [vectorPoly, map_add, Finset.sum_add_distrib]

theorem vectorPoly_smul {n : ℕ} (c : ℚ) (a : Fin n → ℚ) :
    vectorPoly (c • a) = c • vectorPoly a := by
  simp only [vectorPoly, Pi.smul_apply, Finset.smul_sum, Polynomial.smul_monomial]

theorem vectorPoly_coeff {n : ℕ} (a : Fin n → ℚ) (i : Fin n) :
    (vectorPoly a).coeff (i : ℕ) = a i := by
  classical
  simp only [vectorPoly, Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp only [Polynomial.coeff_monomial]
    exact if_neg (fun he => hji (Fin.ext he))
  · simp

theorem vectorPoly_degree {n : ℕ} (a : Fin n → ℚ) :
    (vectorPoly a).natDegree ≤ n-1 := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (Polynomial.natDegree_monomial_le (a i)).trans (by have := i.is_lt; omega)

def weightedPoly (w : V → ℕ) (D : V → ℚ[X]) (k : ℕ)
    (a : ∀ v, Fin (k+1-w v) → ℚ) (v : V) : ℚ[X] :=
  D v * vectorPoly (a v)

omit [Fintype V] [DecidableEq V] in
theorem weightedPoly_degree (w : V → ℕ) (D : V → ℚ[X]) (k : ℕ)
    (a : ∀ v, Fin (k+1-w v) → ℚ)
    (hD : ∀ v, (D v).natDegree ≤ w v) :
    ∀ v, (weightedPoly w D k a v).natDegree ≤ k := by
  intro v
  by_cases hw : w v ≤ k
  · exact Polynomial.natDegree_mul_le.trans
      ((Nat.add_le_add (hD v) (vectorPoly_degree (a v))).trans (by omega))
  · have hn : k+1-w v = 0 := by omega
    have hz : vectorPoly (a v) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have := i.is_lt
      omega
    simp only [weightedPoly, hz, mul_zero, Polynomial.natDegree_zero, Nat.zero_le]

def featureMeasurements (C : M → V → ℚ) (w : V → ℕ)
    (D : V → ℚ[X]) (k : ℕ) :
    (∀ v, Fin (k+1-w v) → ℚ) →ₗ[ℚ] (M → Fin (k+1) → ℚ) where
  toFun a m i := ∑ v, C m v * (weightedPoly w D k a v).coeff (i : ℕ)
  map_add' a b := by
    ext m i
    simp [weightedPoly, vectorPoly_add, mul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    ext m i
    simp only [Pi.smul_apply, weightedPoly, vectorPoly_smul,
      mul_smul_comm, Polynomial.coeff_smul, smul_eq_mul,
      RingHom.id_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun v _ => mul_left_comm _ _ _)

/-- A fully finite feature-count lower bound, proved by injectivity of the
actual coefficientwise measurement map.  Choosing the coordinate vanishing
products gives the weighted binomial square bound. -/
theorem weighted_feature_bound
    (C : M → V → ℚ) (P : V → V → ℚ[X]) (t : I → ℚ)
    (slice : I → V → Prop) (d k : ℕ)
    (w : V → ℕ) (D : V → ℚ[X])
    (ht : Function.Injective t) (ht0 : ∀ i, t i ≠ 0)
    (hP0 : ∀ u v, (P u v).eval 0 = if u = v then 1 else 0)
    (hloc : Locality C P t slice)
    (hPd : ∀ u v, (P u v).natDegree ≤ d)
    (hDdeg : ∀ v, (D v).natDegree ≤ w v)
    (hDne : ∀ v, D v ≠ 0)
    (hDroot : ∀ i v, ¬slice i v → (D v).eval (t i) = 0)
    (hdeg : d + 2*k < Fintype.card I) :
    ∑ v, (k+1-w v) ≤ Fintype.card M * (k+1) := by
  classical
  let T := featureMeasurements C w D k
  have hinj : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro a hTa
    let h := weightedPoly w D k a
    have hd : ∀ v, (h v).natDegree ≤ k := weightedPoly_degree w D k a hDdeg
    have hk : ∀ m, (∑ v, Polynomial.C (C m v) * h v) = 0 := by
      intro m
      apply Polynomial.ext
      intro i
      by_cases hi : i < k+1
      · have he := congrFun (congrFun hTa m) ⟨i,hi⟩
        simpa only [T, featureMeasurements, LinearMap.coe_mk, AddHom.coe_mk,
          Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul,
          Polynomial.coeff_zero, Pi.zero_apply, h] using he
      · have he : (∑ v, Polynomial.C (C m v) * h v).natDegree ≤ k := by
          apply Polynomial.natDegree_sum_le_of_forall_le
          intro v hv
          exact (Polynomial.natDegree_C_mul_le _ _).trans (hd v)
        rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Polynomial.coeff_zero]
    have hs : ∀ i v, ¬slice i v → (h v).eval (t i) = 0 := by
      intro i v hv
      simp only [h, weightedPoly, Polynomial.eval_mul, hDroot i v hv, zero_mul]
    have hh := auxiliary_kernel_zero C P t slice h d k ht ht0 hP0 hloc hk hs hPd hd hdeg
    funext v i
    have hp : vectorPoly (a v) = 0 :=
      (mul_eq_zero.mp (hh v)).resolve_left (hDne v)
    have he := congrArg (fun p : ℚ[X] => p.coeff (i : ℕ)) hp
    simpa only [vectorPoly_coeff, Polynomial.coeff_zero, Pi.zero_apply] using he
  have hr := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_pi_fintype] using hr

#print axioms weighted_feature_bound

def cubeDistance {q : ℕ} (a v : Fin q → Bool) : ℕ :=
  (Finset.univ.filter (fun i => v i ≠ a i)).card

def cubeVanishing {q : ℕ} (t : Fin q → ℚ) (a v : Fin q → Bool) : ℚ[X] :=
  ∏ i ∈ Finset.univ.filter (fun i => v i ≠ a i), (X - Polynomial.C (t i))

/-- The square rank bound in the actual Boolean input coordinates, for
arbitrary rational C and P.  The left side equals the usual weighted
binomial sum; no group invariance or Fourier projection is assumed. -/
theorem cube_feature_bound {q : ℕ}
    (C : M → (Fin q → Bool) → ℚ)
    (P : (Fin q → Bool) → (Fin q → Bool) → ℚ[X])
    (t : Fin q → ℚ) (a : Fin q → Bool) (d k : ℕ)
    (ht : Function.Injective t) (ht0 : ∀ i, t i ≠ 0)
    (hP0 : ∀ u v, (P u v).eval 0 = if u = v then 1 else 0)
    (hloc : Locality C P t (fun i v => v i = a i))
    (hPd : ∀ u v, (P u v).natDegree ≤ d)
    (hdeg : d + 2*k < q) :
    ∑ v : Fin q → Bool, (k+1-cubeDistance a v) ≤ Fintype.card M * (k+1) := by
  classical
  apply weighted_feature_bound C P t (fun i v => v i = a i) d k
    (cubeDistance a) (cubeVanishing t a) ht ht0 hP0 hloc hPd
  · intro v
    unfold cubeVanishing cubeDistance
    calc
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i => v i ≠ a i),
          (X - Polynomial.C (t i) : ℚ[X]).natDegree := Polynomial.natDegree_prod_le _ _
      _ = _ := by simp
  · intro v
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => Polynomial.X_sub_C_ne_zero (t i))
  · intro i v hi
    unfold cubeVanishing
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
    simp
  · simpa only [Fintype.card_fin] using hdeg

#print axioms cube_feature_bound

/-- A binomial form of the complete square measurement bound.  Vertices are
represented by subsets of the q coordinates and the tested half-cube is the
one not containing the given coordinate. -/
theorem boolean_measurement_bound {q : ℕ}
    (C : M → Finset (Fin q) → ℚ)
    (P : Finset (Fin q) → Finset (Fin q) → ℚ[X])
    (t : Fin q → ℚ) (d k : ℕ)
    (ht : Function.Injective t) (ht0 : ∀ i, t i ≠ 0)
    (hP0 : ∀ u v, (P u v).eval 0 = if u = v then 1 else 0)
    (hloc : Locality C P t (fun i S => i ∉ S))
    (hPd : ∀ u v, (P u v).natDegree ≤ d)
    (hdeg : d + 2*k < q) :
    ∑ j ∈ Finset.range (k+1), (k+1-j) * q.choose j ≤ Fintype.card M * (k+1) := by
  classical
  let D : Finset (Fin q) → ℚ[X] := fun S => ∏ i ∈ S, (X - Polynomial.C (t i))
  have hw : ∑ S : Finset (Fin q), (k+1-S.card) ≤ Fintype.card M * (k+1) := by
    apply weighted_feature_bound C P t (fun i S => i ∉ S) d k Finset.card D
      ht ht0 hP0 hloc hPd
    · intro S
      calc
        _ ≤ ∑ i ∈ S, (X - Polynomial.C (t i) : ℚ[X]).natDegree :=
          Polynomial.natDegree_prod_le _ _
        _ = _ := by simp
    · intro S
      exact Finset.prod_ne_zero_iff.mpr (fun i hi => Polynomial.X_sub_C_ne_zero (t i))
    · intro i S hi
      change (∏ j ∈ S, (X - Polynomial.C (t j) : ℚ[X])).eval (t i) = 0
      rw [Polynomial.eval_prod]
      apply Finset.prod_eq_zero (by simpa only [not_not] using hi)
      simp
    · simpa only [Fintype.card_fin] using hdeg
  have hsum : (∑ S : Finset (Fin q), (k+1-S.card)) =
      ∑ j ∈ Finset.range (q+1), (k+1-j) * q.choose j := by
    simpa [mul_comm] using
      (Finset.sum_powerset_apply_card (fun j => k+1-j) (x := (Finset.univ : Finset (Fin q))))
  rw [hsum] at hw
  have hsub : Finset.range (k+1) ⊆ Finset.range (q+1) :=
    Finset.range_mono (by omega)
  have heq : (∑ j ∈ Finset.range (k+1), (k+1-j) * q.choose j) =
      ∑ j ∈ Finset.range (q+1), (k+1-j) * q.choose j := by
    apply Finset.sum_subset hsub
    intro j hj hnot
    have hj' : k+1 ≤ j := by simpa only [Finset.mem_range, not_lt] using hnot
    rw [Nat.sub_eq_zero_of_le hj', zero_mul]
  rw [heq]
  exact hw

#print axioms boolean_measurement_bound

end
end Reconstruction
