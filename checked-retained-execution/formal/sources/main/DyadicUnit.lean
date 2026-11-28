import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! The finite inverse used in P1/P3 is a polynomial over the integral
coefficient ring, evaluated in the receiving ring. No infinite-series
evaluation, canonical integer representative, or nonunit division is used. -/

namespace DyadicUnit
open scoped BigOperators Polynomial

variable {R O : Type*} [CommRing R] [CommRing O]

noncomputable def inverse (a : R) (p : ℕ) : R[X] :=
  ∑ j ∈ Finset.range p, (-Polynomial.C a * Polynomial.X)^j

theorem eval_inverse (φ : R →+* O) (z : O) (a : R) (p : ℕ) :
    (inverse a p).eval₂ φ (2*z) =
      ∑ j ∈ Finset.range p, (-(φ a * (2*z)))^j := by
  let ψ := Polynomial.eval₂RingHom φ (2*z)
  change ψ (inverse a p) = _
  rw [inverse, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_pow, map_mul, map_neg]
  change (-(Polynomial.eval₂ φ (2*z) (Polynomial.C a)) *
    Polynomial.eval₂ φ (2*z) Polynomial.X)^j = _
  rw [Polynomial.eval₂_C, Polynomial.eval₂_X, neg_mul]

theorem unit_inverse (φ : R →+* O) (z : O) (a : R) (p : ℕ) (hnil : (2:O)^p = 0) :
    (1 + φ a * (2*z)) * (inverse a p).eval₂ φ (2*z) = 1 := by
  let x := -(φ a * (2*z))
  have hx : x^p = 0 := by
    have he : x = (-(φ a))* (2*z) := by dsimp [x]; ring
    rw [he, mul_pow, mul_pow, hnil, zero_mul, mul_zero]
  have hg := geom_sum_mul x p
  rw [hx] at hg
  rw [eval_inverse]
  change (1 + φ a * (2*z)) * (∑ j ∈ Finset.range p, x^j) = 1
  have h : 1 + φ a * (2*z) = -(x-1) := by dsimp [x]; ring
  rw [h, neg_mul, mul_comm _ (∑ i ∈ Finset.range p, x^i), hg]
  simp

theorem unit_inverse_power (φ : R →+* O) (z : O) (a : R) (p b : ℕ) (hnil : (2:O)^p = 0) :
    (1 + φ a * (2*z))^(b+1) *
      ((inverse a p)^(b+1)).eval₂ φ (2*z) = 1 := by
  change _ * Polynomial.eval₂RingHom φ (2*z) ((inverse a p)^(b+1)) = _
  rw [map_pow, ← mul_pow]
  change ((1 + φ a * (2*z)) * (inverse a p).eval₂ φ (2*z))^(b+1) = _
  rw [unit_inverse φ z a p hnil, one_pow]

/-- The finite normalized P1 kernel in the formal coordinate 2z. The
coefficients are the already normalized source grid constants and
denominator scalar; they may belong to any integral coefficient ring
mapped into the receiving ring. -/
noncomputable def crossUnit {J : Type*} (s : Finset J) (grid : J → R)
    (scalar denom : R) (p b : ℕ) : R[X] :=
  Polynomial.C scalar * (∏ j ∈ s, (1 + Polynomial.C (grid j) * Polynomial.X)) *
    (inverse denom p)^(b+1)

theorem crossUnit_correct {J : Type*} (φ : R →+* O) (z : O)
    (s : Finset J) (grid : J → R) (scalar denom : R) (p b : ℕ)
    (hnil : (2:O)^p = 0) :
    (crossUnit s grid scalar denom p b).eval₂ φ (2*z) *
      (1 + φ denom * (2*z))^(b+1) =
      φ scalar * ∏ j ∈ s, (1 + φ (grid j) * (2*z)) := by
  let ψ := Polynomial.eval₂RingHom φ (2*z)
  change ψ (crossUnit s grid scalar denom p b) * _ = _
  simp only [crossUnit, map_mul, map_prod, map_add, map_one]
  have hc (a : R) : ψ (Polynomial.C a) = φ a := Polynomial.eval₂_C _ _
  have hX : ψ Polynomial.X = 2*z := Polynomial.eval₂_X _ _
  simp only [hc, hX]
  have hInv : (1 + φ denom * (2*z))^(b+1) *
      ψ ((inverse denom p)^(b+1)) = 1 := unit_inverse_power φ z denom p b hnil
  rw [mul_assoc, mul_comm (ψ (inverse denom p ^ (b+1))), hInv, mul_one]

#print axioms crossUnit_correct
#print axioms eval_inverse
#print axioms unit_inverse
#print axioms unit_inverse_power

end DyadicUnit