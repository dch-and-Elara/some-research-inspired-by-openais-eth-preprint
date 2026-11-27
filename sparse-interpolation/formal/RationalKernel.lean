import RationalTransfer
import Mathlib.RingTheory.Localization.Integral

open Polynomial IsLocalization
open Round4Transfer

namespace GrenetRational

variable {R : Type*} [CommRing R] [Nontrivial R] [IsAddTorsionFree R]

private abbrev Total (R : Type*) [CommRing R] := Localization (nonZeroDivisors R)

omit [Nontrivial R] in
private theorem integer_regular {n : ℤ} (hn : n ≠ 0) :
    (n : R) ∈ nonZeroDivisors R := by
  apply mem_nonZeroDivisors_iff_right.mpr
  intro x hx
  apply zsmul_right_injective hn
  simpa [zsmul_eq_mul, mul_comm] using hx

private theorem int_injective : Function.Injective (Int.castRingHom R) := by
  apply (injective_iff_map_eq_zero (Int.castRingHom R)).mpr
  intro n hn
  by_contra he
  have hr := mem_nonZeroDivisors_iff_right.mp (integer_regular (R := R) he)
  have hz : (1 : R) * (n : R) = 0 := by simpa using hn
  exact one_ne_zero (hr 1 hz)

private noncomputable def rationals : ℚ →+* Total R :=
  IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ)
    (g := (algebraMap R (Total R)).comp (Int.castRingHom R)) fun n =>
      IsLocalization.map_units (Total R)
        ⟨(n.val : R), integer_regular (mem_nonZeroDivisors_iff_ne_zero.mp n.property)⟩

/-- The denominator-cleared polynomial described in Section 5.
Its support is exactly that of H. The coefficient formula displays
the homogeneous scaling by the regular step, and its evaluations
vanish at the original nodes in R. -/
theorem rational_kernel_clearing (a b : R) (A : ℤ) (B : ℕ) (hB : B ≠ 0)
    (hb : b ∈ nonZeroDivisors R) (hRatio : (B : R)*a = (A : R)*b)
    (m : ℕ) (H : ℚ[X]) (hroot : ∀ i : Fin m,
      H.eval (normalizedPrefix ((A : ℚ)/(B : ℚ)) m i) = 0) :
    ∃ (L : ℤ) (P : ℤ[X]) (W : R[X]), L ≠ 0 ∧
      (∀ e, (P.coeff e : ℚ) = (L : ℚ)*H.coeff e) ∧
      (∀ e, W.coeff e = (P.coeff e : R)*b^(H.natDegree-e)) ∧
      W.support = H.support ∧
      (∀ i : Fin m, W.eval (ringPrefix a b m i) = 0) := by
  let P : ℤ[X] := integerNormalization (nonZeroDivisors ℤ) H
  let f : R →+* Total R := algebraMap R _
  let q : ℚ →+* Total R := rationals
  let g := Int.castRingHom R
  let z : ℚ := (A : ℚ)/(B : ℚ)
  let W := (P.map g).scaleRoots b
  obtain ⟨L, hl⟩ := integerNormalization_spec (nonZeroDivisors ℤ) H
  have hl0 : L.val ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp L.property
  have hcoeff (e : ℕ) : (P.coeff e : ℚ) = (L.val : ℚ)*H.coeff e := by
    simpa only [P, Algebra.smul_def] using hl e
  have hs : P.support = H.support := by
    ext i
    have hq : (L.val : ℚ) ≠ 0 := by exact_mod_cast hl0
    simp only [mem_support_iff, ← Int.cast_ne_zero (α := ℚ) (n := P.coeff i), hcoeff,
      mul_ne_zero_iff]
    exact ⟨And.right, fun h => ⟨hq, h⟩⟩
  have hmap : (P.map g).support = H.support := (support_map_of_injective _ int_injective).trans hs
  have hd : (P.map g).natDegree = H.natDegree := by
    rw [Polynomial.natDegree, Polynomial.natDegree]
    unfold Polynomial.degree
    rw [hmap]
  refine ⟨L.val, P, W, hl0, hcoeff, ?_, ?_, ?_⟩
  · intro e
    simp only [W, coeff_scaleRoots, hd, coeff_map, g, Int.coe_castRingHom]
  · rw [support_scaleRoots_eq _ hb, hmap]
  · intro i
    have hf : Function.Injective f := IsLocalization.injective (Total R) le_rfl
    have hBunit : IsUnit (B : Total R) := by
      have hBreg : (B : R) ∈ nonZeroDivisors R := by
        simpa using (integer_regular (R := R) (n := (B : ℤ)) (by exact_mod_cast hB))
      simpa [f] using IsLocalization.map_units (Total R) ⟨(B : R), hBreg⟩
    have hzB : (B : ℚ)*z = (A : ℚ) := by
      dsimp [z]
      rw [mul_comm, div_mul_cancel₀ _ (by exact_mod_cast hB)]
    have hfa : f a = q z * f b := by
      apply sub_eq_zero.mp
      apply hBunit.mul_right_eq_zero.mp
      rw [mul_sub, ← mul_assoc]
      have e1 : (B : Total R)*f a = (A : Total R)*f b := by
        simpa only [map_mul, map_natCast, map_intCast] using congrArg f hRatio
      have e2 : (B : Total R)*q z = (A : Total R) := by
        simpa only [map_mul, map_natCast, map_intCast] using congrArg q hzB
      rw [e1, e2, sub_self]
    have hpoint : f (ringPrefix a b m i) = f b * q (normalizedPrefix z m i) := by
      simp only [ringPrefix, progression, map_add, map_mul, map_natCast,
        normalizedPrefix, normalizedNode, hfa]
      ring
    have hcomp : f.comp g = q.comp (algebraMap ℤ ℚ) := by
      ext j
      simp [g]
    have hP : eval₂ (f.comp g) (q (normalizedPrefix z m i)) P = 0 := by
      rw [hcomp]
      apply integerNormalization_eval₂_eq_zero (nonZeroDivisors ℤ) q H
      rw [eval₂_hom, hroot i, map_zero]
    apply hf
    rw [map_zero, ← eval₂_hom, hpoint]
    change eval₂ f (f b * q (normalizedPrefix z m i)) ((P.map g).scaleRoots b) = 0
    rw [scaleRoots_eval₂_mul, eval₂_map, hP, mul_zero]

end GrenetRational
