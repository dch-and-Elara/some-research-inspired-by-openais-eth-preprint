import GrenetRank
import Degree
import Mathlib.RingTheory.Valuation.Integral

open Polynomial Matrix SharpDifference GrenetResidue
open scoped BigOperators

namespace GrenetRankArendt

private theorem modTwo_nontrivial : Nontrivial ModTwo := by
  refine ⟨⟨1, 0, ?_⟩⟩
  intro he
  have hz : Ideal.Quotient.mk (Ideal.span ({2} : Set D)) (1 : D) = 0 := by
    rw [map_one, he]
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp
    ((Ideal.Quotient.eq_zero_iff_mem).mp hz)
  have hq : (1 : ℚ) = 2 * toRat v := by
    simpa using congrArg toRat hv
  have hhalf : (toRat v : ℚ) = 1/2 := by linarith
  have hmem : toRat v ∈ localTwo := v.property
  rw [hhalf] at hmem
  have hd : ((1/2 : ℚ)).den = 2 := by
    apply Int.ofNat_inj.mp
    simpa only [Int.cast_one, Int.cast_ofNat] using
      Rat.den_div_eq_of_coprime (a := 1) (b := 2) (by decide) (by decide)
  have ho := (mem_localTwo_iff_odd_den _).mp hmem
  rw [hd] at ho
  exact (by decide : ¬ Odd (2 : ℕ)) ho

theorem natDegree_oddFactors (h : ℕ) (E : Fin (2*h) → ℕ) :
    (oddFactors h E).natDegree = (deficit h E)^2 := by
  have hL (s : ℕ) (hs : 0 < s) : (linear s).natDegree = 1 := by
    have hz : (s : D) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
    rw [linear, add_comm, ← C_1, natDegree_add_C, natDegree_C_mul_X _ hz]
  unfold oddFactors
  rw [Polynomial.natDegree_prod _ _ (fun j _ =>
    pow_ne_zero _ (fun h0 => by
      have hz := hL (2*j+1) (by omega)
      rw [h0, natDegree_zero] at hz
      omega))]
  calc
    _ = ∑ j ∈ Finset.range (2*h), GrenetResidue.multiplicity E (2*j+1) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Polynomial.natDegree_pow, hL _ (by omega), mul_one]
    _ = _ := by simpa using sum_center_multiplicities h E 1 (by decide)

/-- The exact degree budget for the residual reciprocal in the paper. -/
theorem normalized_residual_budget (h : ℕ) (E : Fin (2*h) → ℕ)
    (hE : Function.Injective E) (A : LocalPoly) (hf : normalized E = oddFactors h E * A) :
    A.coeff 0 = 1 ∧
      A.natDegree ≤ (∑ i, E i) - (2*h).choose 2 - (deficit h E)^2 := by
  have hP0 : (oddFactors h E).eval 0 = 1 := by
    simp [oddFactors, linear, Polynomial.eval_prod]
  have h0 := normalized_at_zero E hE
  change (normalized E).eval 0 = 1 at h0
  rw [hf, Polynomial.eval_mul, hP0, one_mul, ← Polynomial.coeff_zero_eq_eval_zero] at h0
  have hA : A ≠ 0 := by
    intro hA
    simp [hA] at h0
  have hP : oddFactors h E ≠ 0 := by
    intro hP
    simp [hP] at hP0
  have hd := natDegree_lift_normalized_bound E hE
  change (2*h).choose 2 + ((normalized E).map toRat).natDegree ≤ ∑ i, E i at hd
  rw [Polynomial.natDegree_map_eq_of_injective Subtype.val_injective, hf,
    Polynomial.natDegree_mul hP hA, natDegree_oddFactors] at hd
  exact ⟨h0, by omega⟩

/-- For the exact paper degree budget, the two reflected residuals reduce to the two powers. -/
theorem normalized_residual_reductions (h : ℕ) (E : Fin (2*h) → ℕ)
    (A : LocalPoly) (hr : reducePoly A = 1) :
    let d := (∑ i, E i) - (2*h).choose 2 - (deficit h E)^2
    reducePoly (A.reflect d) = X ^ d ∧
      reducePoly ((A.reflect d).comp (X + 1)) = (X + 1) ^ d := by
  dsimp only
  exact ⟨GrenetRankAlgebra.reflect_reduce modTwo A _ hr,
    GrenetRankAlgebra.reflect_shift_reduce modTwo A _ hr⟩

/-- Only the odd factorization and residual reduction of the one genuine normalized
half-block are supplied. The matrix and integer exceptions follow independently. -/
theorem ordered_full_minor_of_odd_part {K : Type*} [Field K] (q : ℚ →+* K)
    (h : ℕ) (E : Fin (2*h) → ℕ) (hE : Function.Injective E) (z : K)
    (oddPart : ∃ A : LocalPoly, normalized E = oddFactors h E * A ∧ reducePoly A = 1) :
    ∃ rows : Fin (2*h) → Fin (2*(2*h)),
      ((GrenetRank.prefixMatrix z E).submatrix rows id).det ≠ 0 := by
  obtain ⟨A, hf, hred⟩ := oddPart
  letI : IsIntegrallyClosed D :=
    (Valuation.valuationSubring.integers (Rat.padicValuation 2)).isIntegrallyClosed
  letI : Nontrivial ModTwo := modTwo_nontrivial
  obtain ⟨h0, hd⟩ := normalized_residual_budget h E hE A hf
  refine GrenetRank.full_minor_of_normalized_half modTwo q z E hE (exponentV E)
    (exponentV_isUnit hE) (Finset.range (2*h)) (fun i => 2*i+1)
    (fun i => GrenetResidue.multiplicity E (2*i+1)) A _ hd h0 hred ?_
  change (sourceMatrix E).det = _
  rw [normalized_factorization, hf]
  rfl

end GrenetRankArendt
