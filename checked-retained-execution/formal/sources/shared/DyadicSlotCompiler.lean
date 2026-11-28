import LiteralPortCompiler
import NativeInterpolation
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Coeff

/-! P3 dyadic normalization, from the literal-port compiler through
evaluation at one actual receiving-ring probe. The input to this module is
the normalized finite kernels, not an assumption on the completed slot. -/

namespace DyadicSlotCompiler
open LiteralPortCompiler
open scoped BigOperators Polynomial

variable {P M R : Type*} [Fintype P] [DecidableEq P]
  [Fintype M] [DecidableEq M] [CommRing R]

noncomputable section

def order (β : M →₀ ℕ) : ℕ := ∑ m, β m
def valuation (e : M → ℕ) (β : M →₀ ℕ) : ℕ := ∑ m, e m * β m

omit [Fintype P] [DecidableEq P] [DecidableEq M] in
theorem modeWeight_dyadic (e : M → ℕ) (β : M →₀ ℕ) :
    modeWeight (fun m => (Polynomial.C ((2:R)^e m)) * Polynomial.X) β =
      Polynomial.C ((2:R)^valuation e β) * Polynomial.X ^ order β := by
  rw [modeWeight, Finsupp.prod_pow]
  simp only [mul_pow, Finset.prod_mul_distrib,
    order, valuation, ← map_pow, ← map_prod, ← pow_mul, Finset.prod_pow_eq_pow_sum]

/-- Exact P3 receiving-ring identity. Baseline and normalized kernels are
polynomials in the formal coordinate standing for 2z. An actual slot uses
unscaled z for its outer factors and evaluates every original port in the
receiving ring. This is independent of the extraction/evaluation order. -/
theorem p3_evaluated {O : Type*} [CommRing O] (φ : R →+* O) (z : O)
    (F : CNF P) (base : (P → Bool) → P → R[X])
    (unitKernel : (P → Bool) → P → M → R[X])
    (e : M → ℕ) (β : M →₀ ℕ) :
    let eval := fun p : R[X] => p.eval₂ φ (2*z)
    MvPolynomial.coeff β (completed F (fun a p => eval (base a p))
      (fun a p m => (2:O)^e m * z * eval (unitKernel a p m))) =
      (2:O)^valuation e β * z ^ order β *
        eval (MvPolynomial.coeff β (completed F base unitKernel)) := by
  dsimp only
  let ψ : R[X] →+* O := Polynomial.eval₂RingHom φ (2*z)
  change MvPolynomial.coeff β (completed F (fun a p => ψ (base a p))
      (fun a p m => (2:O)^e m * z * ψ (unitKernel a p m))) =
    (2:O)^valuation e β * z ^ order β *
      ψ (MvPolynomial.coeff β (completed F base unitKernel))
  rw [completed_normalized, ← reduce_completed ψ]
  congr 1
  rw [modeWeight, Finsupp.prod_pow]
  simp only [mul_pow, Finset.prod_mul_distrib, order, valuation, ← pow_mul,
    Finset.prod_pow_eq_pow_sum]

omit [Fintype P] [DecidableEq P] [Fintype M] [DecidableEq M] in
theorem eval_truncation {O : Type*} [CommRing O] (φ : R →+* O)
    (p : R[X]) (prec : ℕ) (z : O) (hnil : (2:O)^prec = 0) :
    p.eval₂ φ (2*z) = ∑ j ∈ Finset.range prec, φ (p.coeff j) * (2*z)^j := by
  let n := max prec (p.natDegree+1)
  have hdeg : p.natDegree < n := lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  have he := Polynomial.as_sum_range' p n hdeg
  have hsum : p.eval₂ φ (2*z) =
      ∑ j ∈ Finset.range n, φ (p.coeff j) * (2*z)^j := by
    calc
      _ = Polynomial.eval₂ φ (2*z) (∑ j ∈ Finset.range n, Polynomial.monomial j (p.coeff j)) :=
        congrArg (Polynomial.eval₂ φ (2*z)) he
      _ = _ := by simp [Polynomial.eval₂_finset_sum, Polynomial.eval₂_monomial]
  rw [hsum]
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr (le_max_left _ _))
  intro j _ hj
  have hj' : prec ≤ j := by simpa only [Finset.mem_range, not_lt] using hj
  have hpow : (2*z)^j = 0 := by
    have he : (2:O)^j = 0 := by
      nth_rw 1 [show j = prec + (j-prec) by omega]
      rw [pow_add, hnil, zero_mul]
    rw [mul_pow, he, zero_mul]
  rw [hpow, mul_zero]

/-- J8 coefficient recovery directly from the compiled literal-CNF
completed probes, without assuming that their polynomial representation
has already been supplied. -/
theorem decode_compiled_singleton {O : Type*} [CommRing O]
    (φ : R →+* O) (prec : ℕ) (hp : 0 < prec) (hnil : (2:O)^prec = 0)
    (F : CNF P) (base : (P → Bool) → P → R[X])
    (normalizedKernel : (P → Bool) → P → M → R[X])
    (e : M → ℕ) (m : M) (hv : 1 ≤ e m)
    (x : Fin (prec+1) → O) (hu : ∀ i j, i ≠ j → IsUnit (x j-x i)) :
    let β := Finsupp.single m 1
    let q := MvPolynomial.coeff β (completed F base normalizedKernel)
    let samples := fun i => MvPolynomial.coeff β
      (completed F (fun a p => (base a p).eval₂ φ (2*x i))
        (fun a p j => (2:O)^e j * x i * (normalizedKernel a p j).eval₂ φ (2*x i)))
    NativeInterpolation.decode x samples ⟨1, by omega⟩ =
      (2:O)^e m * φ (q.coeff 0) := by
  dsimp only
  let β := Finsupp.single m 1
  let q := MvPolynomial.coeff β (completed F base normalizedKernel)
  let c := fun j => φ (q.coeff j)
  have he : valuation e β = e m := by
    unfold valuation β
    rw [Finset.sum_eq_single_of_mem m (Finset.mem_univ m)]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
  have hk : order β = 1 := by
    unfold order β
    rw [Finset.sum_eq_single_of_mem m (Finset.mem_univ m)]
    · simp
    · intro j _ hj
      simp [Ne.symm hj]
  have hc (i : Fin (prec+1)) :
      MvPolynomial.coeff β (completed F (fun a p => (base a p).eval₂ φ (2*x i))
        (fun a p j => (2:O)^e j * x i * (normalizedKernel a p j).eval₂ φ (2*x i))) =
        (NativeInterpolation.normalized prec (e m) 1 c).eval (x i) := by
    rw [p3_evaluated, he, hk, NativeInterpolation.normalized_eval]
    change (2:O)^e m * (x i)^1 * q.eval₂ φ (2*x i) = _
    rw [eval_truncation φ q prec (x i) hnil]
  change NativeInterpolation.decode x _ _ = (2:O)^e m * c 0
  rw [show (fun i => MvPolynomial.coeff β
      (completed F (fun a p => (base a p).eval₂ φ (2*x i))
        (fun a p j => (2:O)^e j * x i * (normalizedKernel a p j).eval₂ φ (2*x i)))) =
      (fun i => (NativeInterpolation.normalized prec (e m) 1 c).eval (x i)) from funext hc]
  exact NativeInterpolation.singleton_from_completed_probes prec (e m) c hp hv hnil x hu

#print axioms decode_compiled_singleton
#print axioms eval_truncation
#print axioms modeWeight_dyadic
#print axioms p3_evaluated
end
end DyadicSlotCompiler