import StrictAlternant
import StrictDenominator
import Mathlib.LinearAlgebra.Matrix.Rank

open scoped BigOperators fwdDiff
open Polynomial SharpDifference

namespace GrenetStrict

noncomputable def affineMatrix {k : ℕ} (c : ℚ) (E : Fin k → ℕ) : Matrix (Fin k) (Fin k) ℚ :=
  Matrix.of fun i j => (1 + (i.val : ℚ)*c)^E j

noncomputable def prefixMatrix {k : ℕ} (z : ℚ) (E : Fin k → ℕ) : Matrix (Fin k) (Fin k) ℚ :=
  Matrix.of fun i j => (z + (i.val : ℚ))^E j

private def specialize (c : ℚ) : UPoly →+* ℚ := Polynomial.evalRingHom (c/2)

private theorem specialize_twoU (c : ℚ) : specialize c twoU = c := by
  change (2 * (X : ℚ[X])).eval (c/2) = c
  simp
  ring

private theorem specialize_source {k : ℕ} (c : ℚ) (E : Fin k → ℕ) :
    (sourceMatrix E).map (specialize c) = affineMatrix c E := by
  apply Matrix.ext
  intro i j
  change specialize c ((1 + (i.val : UPoly)*twoU)^E j) = (1 + (i.val : ℚ)*c)^E j
  simp only [map_pow, map_add, map_one, map_mul, map_natCast, specialize_twoU]

variable (p : ℕ) [Fact p.Prime]

noncomputable def localRowMatrix {k : ℕ} (c : ℚ) (hc : StrictStep p c)
    (M : ℕ) (E : Fin k → ℕ) : Matrix (Fin k) (Fin k) (D p) :=
  Matrix.of fun i j => (rowPoly p c hc M i.val).eval (E j : D p)

private theorem diff_mul {k : ℕ} (c : ℚ) (hc : StrictStep p c) (M : ℕ)
    (E : Fin k → ℕ) (hE : ∀ j, E j ≤ M) :
    (differenceMatrix k).map (specialize c) * affineMatrix c E =
      Matrix.of (fun i j => c^i.val * toRat p (localRowMatrix p c hc M E i j)) := by
  rw [← specialize_source c E, ← Matrix.map_mul]
  apply Matrix.ext
  intro i j
  change specialize c ((differenceMatrix k * sourceMatrix E) i j) =
    c^i.val * toRat p ((rowPoly p c hc M i.val).eval (E j : D p))
  rw [differenceMatrix_entry]
  change (specialize c).toAddMonoidHom
      ((Δ_[1]^[i.val] (fun l : ℕ => (1 + (l : UPoly)*twoU)^E j)) 0) = _
  rw [map_fwdDiff]
  have he : (specialize c).toAddMonoidHom ∘ (fun l : ℕ => (1 + (l : UPoly)*twoU)^E j) =
      (fun l : ℕ => (1 + (l : ℚ)*c)^E j) := by
    funext l
    change specialize c ((1 + (l : UPoly)*twoU)^E j) = _
    simp only [map_pow, map_add, map_one, map_mul, map_natCast, specialize_twoU]
  rw [he, fwdDiff_row p c hc M (E j) i.val (hE j)]

theorem determinant_row_factor {k : ℕ} (c : ℚ) (hc : StrictStep p c) (M : ℕ)
    (E : Fin k → ℕ) (hE : ∀ j, E j ≤ M) :
    (affineMatrix c E).det = c^k.choose 2 * toRat p (localRowMatrix p c hc M E).det := by
  have hd : ((differenceMatrix k).map (specialize c)).det = 1 := by
    change ((specialize c).mapMatrix (differenceMatrix k)).det = 1
    rw [← RingHom.map_det, det_differenceMatrix, map_one]
  have h := congrArg Matrix.det (diff_mul p c hc M E hE)
  rw [Matrix.det_mul, hd, one_mul] at h
  rw [RingHom.map_det]
  rw [h, Matrix.det_mul_column, Finset.prod_pow_eq_pow_sum]
  have hsum : (∑ i : Fin k, i.val) = k.choose 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) k, Finset.sum_range_id, Nat.choose_two_right]
  rw [hsum]
  rfl

private theorem map_vandermonde_det {k : ℕ} (E : Fin k → ℕ) :
    toRat p (Matrix.vandermonde (fun j => (E j : D p))).det =
      (Matrix.vandermonde (fun j => (E j : ℚ))).det := by
  rw [RingHom.map_det]
  congr 1

/-- Strict normalized determinant has residue 1. The exponent Vandermonde
is evaluated only after the symbolic division. -/
theorem strict_normalized_residue_one {k : ℕ} (c : ℚ) (hc : StrictStep p c)
    (E : Fin k → ℕ) :
    ∃ N : D p, residue p N = 1 ∧
      (affineMatrix c E).det =
        c^k.choose 2 * (Matrix.vandermonde (fun j => (E j : ℚ))).det * toRat p N := by
  let M : ℕ := Finset.univ.sup E + k
  have he (j : Fin k) : E j ≤ M := (Finset.le_sup (f := E) (Finset.mem_univ j)).trans
    (Nat.le_add_right _ _)
  have hm (i : Fin k) : i.val ≤ M := by have hi := i.isLt; dsimp [M]; omega
  obtain ⟨Q, hQ, hQone⟩ := strict_symbolic_quotient p c hc k M hm
  let N : D p := MvPolynomial.eval (fun j => (E j : D p)) Q
  refine ⟨N, ?_, ?_⟩
  · change residue p (MvPolynomial.eval (fun j => (E j : D p)) Q) = 1
    rw [MvPolynomial.eval₂_comp, ← MvPolynomial.eval_map, hQone, map_one]
  · have hd := congrArg (MvPolynomial.eval (fun j => (E j : D p))) hQ
    rw [eval_alternant_det, map_mul, eval_symbolicV] at hd
    change (localRowMatrix p c hc M E).det =
      (Matrix.vandermonde (fun j => (E j : D p))).det * N at hd
    rw [determinant_row_factor p c hc M E he, hd, map_mul, map_vandermonde_det, mul_assoc]

theorem affine_det_ne_zero_of_strict {k : ℕ} (c : ℚ) (hc : StrictStep p c)
    (E : Fin k → ℕ) (hE : Function.Injective E) : (affineMatrix c E).det ≠ 0 := by
  obtain ⟨N, hN, hd⟩ := strict_normalized_residue_one p c hc E
  rw [hd]
  have hv : (Matrix.vandermonde (fun j => (E j : ℚ))).det ≠ 0 := by
    apply Matrix.det_vandermonde_ne_zero_iff.mpr
    intro i j hij
    apply hE
    exact_mod_cast (show (E i : ℚ) = (E j : ℚ) from hij)
  have hu : IsUnit N :=
    (IsLocalRing.residue_ne_zero_iff_isUnit N).mp (by rw [hN]; exact one_ne_zero)
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (strictStep_ne_zero p hc)) hv)
    (hu.map (toRat p)).ne_zero

open scoped BigOperators in
private theorem prefix_det_factor {k : ℕ} (z : ℚ) (hz : z ≠ 0) (E : Fin k → ℕ) :
    (prefixMatrix z E).det = (∏ j, z^E j) * (affineMatrix z⁻¹ E).det := by
  have he : prefixMatrix z E = Matrix.of (fun i j => z^E j * affineMatrix z⁻¹ E i j) := by
    apply Matrix.ext
    intro i j
    change (z + (i.val : ℚ))^E j = z^E j * (1 + (i.val : ℚ)*z⁻¹)^E j
    rw [← mul_pow]
    congr 1
    rw [mul_add, mul_one, ← mul_left_comm, mul_inv_cancel₀ hz, mul_one]
  rw [he, Matrix.det_mul_row]

theorem prefix_det_ne_zero_of_den_gt_two {k : ℕ} (z : ℚ) (hz : 2 < z.den)
    (E : Fin k → ℕ) (hE : Function.Injective E) : (prefixMatrix z E).det ≠ 0 := by
  obtain ⟨p, hp, hc⟩ := exists_strict_prime_of_den z hz
  letI : Fact p.Prime := ⟨hp⟩
  have hz0 : z ≠ 0 := by
    intro he
    simp [he] at hz
  rw [prefix_det_factor z hz0 E]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun _ _ => pow_ne_zero _ hz0))
    (affine_det_ne_zero_of_strict p z⁻¹ hc E hE)

/-- No degree bound, sign hypothesis or rank hypothesis. -/
theorem prefix_det_ne_zero_of_nonhalf {k : ℕ} (z : ℚ)
    (hz : ¬ ∃ a : ℤ, 2*z = (a : ℚ)) (E : Fin k → ℕ)
    (hE : Function.Injective E) : (prefixMatrix z E).det ≠ 0 :=
  prefix_det_ne_zero_of_den_gt_two z (den_gt_two_of_nonhalf z hz) E hE

theorem prefix_full_column_rank_of_nonhalf {k : ℕ} (z : ℚ)
    (hz : ¬ ∃ a : ℤ, 2*z = (a : ℚ)) (E : Fin k → ℕ)
    (hE : Function.Injective E) : (prefixMatrix z E).rank = k := by
  have hd := isUnit_iff_ne_zero.mpr (prefix_det_ne_zero_of_nonhalf z hz E hE)
  have h := Matrix.rank_mul_eq_left_of_isUnit_det (prefixMatrix z E)
    (1 : Matrix (Fin k) (Fin k) ℚ) hd
  simpa [Matrix.rank_one] using h

end GrenetStrict

