import GrenetSameSign
import GrenetRankAlgebra
import Upper

open Polynomial Matrix
open scoped BigOperators

namespace GrenetRank

variable {k : ℕ} {K : Type*} [Field K]

/-- Rows indexed by the complete prefix. -/
def prefixMatrix (z : K) (e : Fin k → ℕ) : Matrix (Fin (2*k)) (Fin k) K :=
  Matrix.of fun i j => (z + (i.val : K)) ^ e j

/-- The two interleaved half-blocks. -/
def halfMatrix (x : K) (e : Fin k → ℕ) : Matrix (Fin k) (Fin k) K :=
  Matrix.of fun i j => (x + (i.val : K)*2) ^ e j

/-- The original affine-in-U half-block before reciprocation. -/
noncomputable def source (e : Fin k → ℕ) : Matrix (Fin k) (Fin k) ℚ[X] :=
  Matrix.of fun i j => (1 + (i.val : ℚ[X]) * (2 * X)) ^ e j

theorem rational_prefix_minor (q : ℚ →+* K) (z : ℚ) (e : Fin k → ℕ)
    (he : Function.Injective e) :
    ∃ rows : Fin k → Fin (2*k), ((prefixMatrix (q z) e).submatrix rows id).det ≠ 0 := by
  classical
  let o : ℕ := if 0 < z + (k : ℚ) then k else 0
  let rows (i : Fin k) : Fin (2*k) := ⟨o + i.val, by
    have hi := i.isLt
    by_cases h : 0 < z + (k : ℚ) <;> simp [o, h] <;> omega⟩
  let x (i : Fin k) : ℚ := z + (rows i).val
  have hx : Function.Injective x := by
    intro i j hij
    have hcast : ((rows i).val : ℚ) = ((rows j).val : ℚ) := add_left_cancel hij
    have hv := Nat.cast_injective (R := ℚ) hcast
    apply Fin.ext
    exact Nat.add_left_cancel hv
  have hs : (∀ i, 0 < x i) ∨ (∀ i, x i < 0) := by
    by_cases h : 0 < z + (k : ℚ)
    · left
      intro i
      change 0 < z + (((o + i.val : ℕ)) : ℚ)
      simp only [o, if_pos h, Nat.cast_add]
      linarith [Nat.cast_nonneg (α := ℚ) i.val]
    · right
      intro i
      change z + (((o + i.val : ℕ)) : ℚ) < 0
      simp only [o, if_neg h, zero_add]
      have hi : (i.val : ℚ) < k := by exact_mod_cast i.isLt
      linarith
  have hR := GrenetSameSign.det_pow_ne_zero_rat x e hx he hs
  refine ⟨rows, ?_⟩
  have hM : q.mapMatrix (Matrix.of fun i j => x i ^ e j) =
      (prefixMatrix (q z) e).submatrix rows id := by
    ext i j
    change q ((z + ((rows i).val : ℚ)) ^ e j) = (q z + ((rows i).val : K)) ^ e j
    rw [map_pow, map_add, map_natCast]
  rw [← hM, ← RingHom.map_det]
  exact (map_ne_zero_iff q q.injective).mpr hR

private theorem eval_source_eq_scaled (q : ℚ →+* K) (x : K) (hx : x ≠ 0) (e : Fin k → ℕ) :
    (eval₂RingHom q x⁻¹).mapMatrix (source e) =
      halfMatrix x e * Matrix.diagonal (fun j => (x⁻¹) ^ e j) := by
  ext i j
  rw [Matrix.mul_diagonal]
  change (eval₂RingHom q x⁻¹) ((1 + (i.val : ℚ[X]) * (2 * X)) ^ e j) =
    (x + (i.val : K)*2)^e j * (x⁻¹)^e j
  rw [map_pow, map_add, map_mul, map_mul, map_one, map_natCast]
  rw [show (eval₂RingHom q x⁻¹) (X : ℚ[X]) = x⁻¹ from eval₂_X q x⁻¹]
  rw [map_ofNat, ← mul_pow]
  congr 1
  rw [add_mul, mul_inv_cancel₀ hx, mul_assoc]

private theorem residual_zero_of_singular_half {D : Type*} [CommRing D]
    [Algebra D ℚ] (q : ℚ →+* K) (x : K)
    (hx : ∀ w : ℤ, x ≠ q (w : ℚ)) (e : Fin k → ℕ) (V : ℚ[X]) (hV : IsUnit V)
    (S : Finset ℕ) (c m : ℕ → ℕ) (A : D[X]) (d : ℕ) (hd : A.natDegree ≤ d)
    (hnorm : (source e).det = (2 * X)^k.choose 2 * V *
      ((∏ j ∈ S, (1 + C (c j : D) * X)^m j) * A).map (algebraMap D ℚ))
    (hsing : (halfMatrix x e).det = 0) :
    ((A.reflect d).map (algebraMap D ℚ)).eval₂ q x = 0 := by
  let ev := eval₂RingHom q x⁻¹
  have hx0 : x ≠ 0 := by simpa using hx 0
  have hz : ev (source e).det = 0 := by
    rw [RingHom.map_det, eval_source_eq_scaled q x hx0 e, Matrix.det_mul, hsing, zero_mul]
  rw [hnorm, map_mul, map_mul, map_pow, map_mul] at hz
  have h2 : ev (2 : ℚ[X]) ≠ 0 := by
    rw [show (2 : ℚ[X]) = C (2 : ℚ) from (C_eq_natCast 2).symm]
    change eval₂ q x⁻¹ (C 2) ≠ 0
    rw [eval₂_C]
    exact (map_ne_zero_iff q q.injective).mpr (by norm_num)
  have hX : ev (X : ℚ[X]) ≠ 0 := by
    rw [show ev (X : ℚ[X]) = x⁻¹ from eval₂_X q x⁻¹]
    exact inv_ne_zero hx0
  have hb : ev (((∏ j ∈ S, (1 + C (c j : D) * X)^m j) * A).map (algebraMap D ℚ)) = 0 :=
    (mul_eq_zero.mp hz).resolve_left
      (mul_ne_zero (pow_ne_zero _ (mul_ne_zero h2 hX)) (hV.map ev).ne_zero)
  rw [Polynomial.map_mul, map_mul] at hb
  have hP : ev ((∏ j ∈ S, (1 + C (c j : D) * X)^m j : D[X]).map (algebraMap D ℚ)) ≠ 0 := by
    rw [Polynomial.map_prod, map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    rw [Polynomial.map_pow, map_pow]
    apply pow_ne_zero
    intro h
    have hh : 1 + (c i : K) * x⁻¹ = 0 := by
      simpa [ev, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, eval₂_C] using h
    have hh' : (1 + (c i : K) * x⁻¹) * x = 0*x := congrArg (fun y : K => y*x) hh
    rw [add_mul, one_mul, mul_assoc, inv_mul_cancel₀ hx0, mul_one, zero_mul] at hh'
    exact hx (-(c i : ℤ)) (by
      rw [Int.cast_neg, Int.cast_natCast, map_neg, map_natCast]
      exact eq_neg_of_add_eq_zero_left hh')
  have hzero : eval₂ q x⁻¹ (A.map (algebraMap D ℚ)) = 0 :=
    (mul_eq_zero.mp hb).resolve_left hP
  letI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx0)
  have hdeg : (A.map (algebraMap D ℚ)).natDegree ≤ d :=
    natDegree_map_le.trans hd
  have h := (eval₂_reflect_eq_zero_iff q x⁻¹ d (A.map (algebraMap D ℚ)) hdeg).mpr hzero
  rwa [invOf_eq_inv, inv_inv, reflect_map] at h

/-- No simultaneous singularity outside rational integer starts follows from the one concrete
normalized polynomial and the residue of its explicit residual factor. -/
theorem full_minor_of_normalized_half {D F : Type*} [CommRing D] [IsDomain D]
    [IsIntegrallyClosed D] [Algebra D ℚ] [IsFractionRing D ℚ] [CommRing F] [Nontrivial F]
    (red : D →+* F) (q : ℚ →+* K) (z : K) (e : Fin k → ℕ)
    (he : Function.Injective e) (V : ℚ[X]) (hV : IsUnit V)
    (S : Finset ℕ) (c m : ℕ → ℕ) (A : D[X]) (d : ℕ)
    (hd : A.natDegree ≤ d) (h0 : A.coeff 0 = 1) (hr : A.map red = 1)
    (hnorm : (source e).det = (2 * X)^k.choose 2 * V *
      ((∏ j ∈ S, (1 + C (c j : D) * X)^m j) * A).map (algebraMap D ℚ)) :
    ∃ rows : Fin k → Fin (2*k), ((prefixMatrix z e).submatrix rows id).det ≠ 0 := by
  by_cases hz : ∃ w : ℤ, z = q (w : ℚ)
  · obtain ⟨w, rfl⟩ := hz
    exact rational_prefix_minor q w e he
  · have hzn (w : ℤ) : z ≠ q (w : ℚ) := fun h => hz ⟨w, h⟩
    have hz1 (w : ℤ) : z + 1 ≠ q (w : ℚ) := by
      intro h
      apply hzn (w-1)
      rw [Int.cast_sub, Int.cast_one, map_sub, map_one, ← h, add_sub_cancel_right]
    have hh : (halfMatrix z e).det ≠ 0 ∨ (halfMatrix (z+1) e).det ≠ 0 := by
      by_contra! hh
      have h₀ := residual_zero_of_singular_half q z hzn e V hV S c m A d hd hnorm hh.1
      have h₁ := residual_zero_of_singular_half q (z+1) hz1 e V hV S c m A d hd hnorm hh.2
      have hco := GrenetRankAlgebra.isCoprime_reflect_shift (K := ℚ) red A d hd h0 hr
      obtain ⟨u, v, huv⟩ := hco
      have H := congrArg (eval₂RingHom q z) huv
      have h₁' : eval₂ q z (((A.reflect d).comp (X + 1)).map (algebraMap D ℚ)) = 0 := by
        rw [map_comp]
        simpa [eval₂_comp] using h₁
      simp only [map_add, map_mul, map_one] at H
      change _ * eval₂ q z ((A.reflect d).map (algebraMap D ℚ)) +
        _ * eval₂ q z (((A.reflect d).comp (X+1)).map (algebraMap D ℚ)) = 1 at H
      rw [h₀, h₁', mul_zero, mul_zero, add_zero] at H
      exact zero_ne_one H
    rcases hh with hL | hR
    · let rows (i : Fin k) : Fin (2*k) := ⟨i.val*2, by have := i.isLt; omega⟩
      refine ⟨rows, ?_⟩
      have hm : (prefixMatrix z e).submatrix rows id = halfMatrix z e := by
        ext i j
        change (z + ((i.val*2 : ℕ) : K))^e j = (z + (i.val : K)*2)^e j
        rw [Nat.cast_mul, Nat.cast_ofNat]
      rw [hm]
      exact hL
    · let rows (i : Fin k) : Fin (2*k) := ⟨i.val*2+1, by have := i.isLt; omega⟩
      refine ⟨rows, ?_⟩
      have hm : (prefixMatrix z e).submatrix rows id = halfMatrix (z+1) e := by
        ext i j
        change (z + ((i.val*2+1 : ℕ) : K))^e j = (z + 1 + (i.val : K)*2)^e j
        rw [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
        ring_nf
      rw [hm]
      exact hR

end GrenetRank
