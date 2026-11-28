import J9EndGeometry

/-! A literal global completed singleton: one actual target port is
marked and the other binary rows retain their original multilinear
equality factors. The complete Boolean column cube is summed before
coefficient projection. The higher-order terms need not be bounded. -/

namespace J9End
open scoped BigOperators Polynomial Classical
open Polynomial

noncomputable section
variable {L M : ℕ} {R T : Type*} [Fintype R] [DecidableEq R] [Fintype T]
variable (g : J9FactorBounds.Chart L M R T)

def rowArgument (tail : (Fin M → Bool) → R → Bool → ℚ[X])
    (x : Fin M → Bool) (r : R) (b : Bool) : ℚ[X] :=
  C ((J9FactorBounds.arg (J9FactorBounds.kernel L) (g.hit r b) (x (g.rowInput r b)) : ℤ) : ℚ)
    + X * tail x r b

def unmarked (tail : (Fin M → Bool) → R → Bool → ℚ[X])
    (x : Fin M → Bool) (r : R) : ℚ[X] :=
  TargetDerivative.equality (rowArgument g tail x r false) (rowArgument g tail x r true)

def marked (tail : (Fin M → Bool) → R → Bool → ℚ[X])
    (x : Fin M → Bool) (i : Fin L) : ℚ[X] :=
  if g.leg i then
    TargetDerivative.equality (rowArgument g tail x (g.rowOf i) false) 1 -
      TargetDerivative.equality (rowArgument g tail x (g.rowOf i) false) 0
  else
    TargetDerivative.equality 1 (rowArgument g tail x (g.rowOf i) true) -
      TargetDerivative.equality 0 (rowArgument g tail x (g.rowOf i) true)

def outerDistance (i : Fin L) : ℚ :=
  ((L:ℤ)-1-(g.tau.val:ℤ)+(i.val:ℤ) : ℤ)

def crossing (b : ℕ) (tail : Fin L → ℚ[X]) (i : Fin L) : ℚ[X] :=
  J8SourceMoment.outerKernel (J9FactorBounds.kernel L) (2*(L:ℚ))
    (outerDistance g i) b (tail i)

def columnWeight (b : ℕ) (tail : (Fin M → Bool) → ℚ[X]) (x : Fin M → Bool) : ℚ[X] :=
  C (if g.table x then 1 else 0) *
    (C (J9FactorBounds.moment g b x : ℚ) + X * tail x)

/-- Rows and both Boolean legs are indexed by real ports, never padding.
The target row is replaced by its signed difference, not by its
unmarked value and not by a new independently chosen assignment. -/
def literalCompleted (b : ℕ)
    (rows : (Fin M → Bool) → R → Bool → ℚ[X])
    (cross : Fin L → ℚ[X]) (source : (Fin M → Bool) → ℚ[X]) : ℚ[X] :=
  ∑ i ∈ g.targets, crossing g b cross i *
    ∑ x : Fin M → Bool, columnWeight g b source x * marked g rows x i *
      ∏ r ∈ (Finset.univ : Finset R).erase (g.rowOf i), unmarked g rows x r

omit [Fintype R] [DecidableEq R] [Fintype T] in
theorem unmarked_coeff_zero (tail : (Fin M → Bool) → R → Bool → ℚ[X])
    (x : Fin M → Bool) (r : R) :
    (unmarked g tail x r).coeff 0 =
      (J9FactorBounds.rowBase (J9FactorBounds.kernel L) (g.hit r)
        (fun k => x (g.rowInput r k)) : ℚ) := by
  simp [unmarked, rowArgument, TargetDerivative.equality, Polynomial.mul_coeff_zero,
    Polynomial.coeff_sub, J9FactorBounds.rowBase, J9FactorBounds.equalityPoly]
  ring

omit [Fintype R] [DecidableEq R] [Fintype T] in
theorem marked_coeff_zero (tail : (Fin M → Bool) → R → Bool → ℚ[X])
    (x : Fin M → Bool) (i : Fin L) :
    (marked g tail x i).coeff 0 = (J9FactorBounds.difference g i x : ℚ) := by
  have hzero (f : ℚ[X]) : (f.coeff 0) = f.eval 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]
  rw [hzero]
  unfold marked J9FactorBounds.difference J9FactorBounds.rowDiff
  cases h : g.leg i <;>
    simp [TargetDerivative.equality, rowArgument, J9FactorBounds.equalityPoly] <;>
    ring

omit [Fintype R] [DecidableEq R] [Fintype T] in
theorem crossing_coeff_one (b : ℕ) (tail : Fin L → ℚ[X]) (i : Fin L) :
    (crossing g b tail i).coeff 1 =
      (J9FactorBounds.slope L b : ℚ) / J9FactorBounds.denominator g b i := by
  simp only [crossing, J8SourceMoment.outerKernel_first, J8SourceMoment.exactSlope,
    J9FactorBounds.slope, J9FactorBounds.denominator, outerDistance]
  push_cast
  rfl

theorem target_sum_coeff_zero (b : ℕ)
    (rows : (Fin M → Bool) → R → Bool → ℚ[X])
    (source : (Fin M → Bool) → ℚ[X]) (i : Fin L) :
    (∑ x : Fin M → Bool, columnWeight g b source x * marked g rows x i *
      ∏ r ∈ (Finset.univ : Finset R).erase (g.rowOf i), unmarked g rows x r).coeff 0 =
      (∑ x : Fin M → Bool, J9FactorBounds.term g b i x : ℤ) := by
  rw [finset_sum_coeff, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Polynomial.mul_coeff_zero, Polynomial.coeff_zero_prod, marked_coeff_zero,
    unmarked_coeff_zero, columnWeight, Polynomial.coeff_add, Polynomial.coeff_C_zero,
    Polynomial.coeff_X_zero, zero_mul, add_zero,
    J9FactorBounds.term, J9FactorBounds.baseline, Int.cast_mul, Int.cast_prod]
  cases h : g.table x <;> simp

/-- The signed first coefficient used by the size proof is precisely the
linear coefficient of this source contraction on all column assignments. -/
theorem literal_first_exact (b : ℕ)
    (rows : (Fin M → Bool) → R → Bool → ℚ[X])
    (cross : Fin L → ℚ[X]) (source : (Fin M → Bool) → ℚ[X]) :
    (literalCompleted g b rows cross source).coeff 1 = J9FactorBounds.firstCoeff g b := by
  rw [literalCompleted, finset_sum_coeff, J9FactorBounds.firstCoeff]
  apply Finset.sum_congr rfl
  intro i hi
  have hz : (crossing g b cross i).coeff 0 = 0 :=
    J8SourceMoment.outerKernel_zero _ _ _ _ _
  rw [TargetDerivative.first_mul_vanishing_target _ _ hz,
    crossing_coeff_one, target_sum_coeff_zero, Int.cast_mul, div_mul_eq_mul_div]

#print axioms unmarked_coeff_zero
#print axioms marked_coeff_zero
#print axioms literal_first_exact
end
end J9End

