import J9LayoutTransferCompiler

/-! Literal exact normalization at the actual J9 target addresses.
No low-ring congruence or derivative-factor match is assumed. -/
namespace J9LayoutTransfer

open scoped BigOperators Classical
open LiteralPortCompiler
noncomputable section
variable {L M : ℕ} {R T : Type*} [Fintype R] [DecidableEq R] [Fintype T]

def chartBase (g : J9FactorBounds.Chart L M R T) (x : Fin M → Bool) (p : Port R) : ℚ :=
  (J9FactorBounds.arg (J9FactorBounds.kernel L) (g.hit p.1 p.2) (x (g.rowInput p.1 p.2)) : ℤ)

def chartWeight (g : J9FactorBounds.Chart L M R T) (b : ℕ) (x : Fin M → Bool) : ℚ :=
  (if g.table x then 1 else 0) * (J9FactorBounds.moment g b x : ℚ)

def chartOther (g : J9FactorBounds.Chart L M R T) (x : Fin M → Bool) (p : Port R) : ℚ :=
  (-1 + 2 * chartBase g x (p.1,!p.2)) *
    ∏ r ∈ (Finset.univ : Finset R).erase p.1,
      TargetDerivative.equality (chartBase g x (r,false)) (chartBase g x (r,true))

omit [Fintype R] [DecidableEq R] [Fintype T] in
theorem chart_unmarked_exact (g : J9FactorBounds.Chart L M R T) (x : Fin M → Bool) (r : R) :
    TargetDerivative.equality (chartBase g x (r,false)) (chartBase g x (r,true)) =
      (J9FactorBounds.rowBase (J9FactorBounds.kernel L) (g.hit r)
        (fun k => x (g.rowInput r k)) : ℚ) := by
  unfold TargetDerivative.equality chartBase J9FactorBounds.rowBase J9FactorBounds.equalityPoly
  push_cast
  ring

theorem chartOther_factor (g : J9FactorBounds.Chart L M R T) (b : ℕ) (x : Fin M → Bool) (i : Fin L) :
    chartWeight g b x * chartOther g x (g.rowOf i,g.leg i) =
      (J9FactorBounds.term g b i x : ℚ) := by
  simp only [chartWeight, chartOther, chart_unmarked_exact,
    J9FactorBounds.term, J9FactorBounds.baseline, J9FactorBounds.difference,
    J9FactorBounds.rowDiff_formula, Int.cast_mul, Int.cast_prod, Int.cast_add,
    Int.cast_ofNat, Int.cast_neg, Int.cast_one]
  unfold chartBase
  cases g.table x
  · simp
  · simp
    ring

variable {Packet S V G : Type*} {P : V → Type*}
variable [Fintype Packet] [DecidableEq Packet] [DecidableEq G]
variable (d : J8Physical.Layout Packet R S V G P L)

def chartKernel (anchor : S) (idx : Port R ≃ Fin M) (truth : (Fin M → Bool) → Bool)
    (b : ℕ) (p : Port R) : ℚ :=
  if p ∈ J8Physical.targets d (J8Physical.pinWire d anchor) then
    (J9FactorBounds.kernel L : ℚ) /
      J9FactorBounds.denominator (J9End.chart d anchor idx truth) b (J9End.slot d p)
  else 0

/-- No formal mode coefficient or signed row difference is assumed: the
identity is a literal native coefficient summed against one complete
column assignment and transported along its true target-slot map. -/
theorem normalized_rows_one_assignment (anchor : S) (idx : Port R ≃ Fin M)
    (truth : (Fin M → Bool) → Bool) (b : ℕ) (x : Fin M → Bool) :
    let g := J9End.chart d anchor idx truth
    ((2:ℚ)*(L:ℚ)*2^b) * (chartWeight g b x *
        MvPolynomial.coeff β (rowCompiler (chartBase g x) (chartKernel d anchor idx truth b))) =
      ∑ i ∈ g.targets, ((J9FactorBounds.slope L b : ℚ) /
        J9FactorBounds.denominator g b i) * (J9FactorBounds.term g b i x : ℚ) := by
  dsimp only
  let g := J9End.chart d anchor idx truth
  let κ := chartKernel d anchor idx truth b
  let tgt := J8Physical.targets d (J8Physical.pinWire d anchor)
  let fac := (2:ℚ)*(L:ℚ)*2^b
  have hs :
      MvPolynomial.coeff β (rowCompiler (chartBase g x) κ) =
        ∑ p ∈ tgt, κ p * chartOther g x p := by
    rw [singleton_native_rows]
    simp only [chartOther, mul_assoc]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    have hk : κ p = 0 := by simpa [κ, chartKernel, tgt] using
      (if_neg hp : (if p ∈ tgt then
        (J9FactorBounds.kernel L : ℚ) / J9FactorBounds.denominator g b (J9End.slot d p)
        else 0) = 0)
    rw [hk, zero_mul]
  change fac * (chartWeight g b x * MvPolynomial.coeff β (rowCompiler (chartBase g x) κ)) = _
  rw [hs]
  simp only [Finset.mul_sum]
  rw [← sum_actual_target_slots d anchor
    (fun p => fac * (chartWeight g b x * (κ p * chartOther g x p)))]
  apply Finset.sum_congr rfl
  intro i hi
  let p := J9End.targetWire d anchor i
  obtain ⟨hp, hi'⟩ := J9End.targetWire_spec d anchor hi
  have hk : κ p = (J9FactorBounds.kernel L : ℚ) / J9FactorBounds.denominator g b i := by
    dsimp [κ, chartKernel,p]
    rw [if_pos hp, hi']
  have hm := chartOther_factor g b x i
  change chartWeight g b x * chartOther g x p = _ at hm
  rw [hk, ← hm]
  unfold fac J9FactorBounds.slope
  push_cast
  ring

/-- Aggregate literal normalized singleton coefficient for the complete
column Boolean cube. Multiplication by the native outer scale recovers
the signed first coefficient already used in the centered-lift theorem. -/
theorem normalized_rows_full_cube (anchor : S) (idx : Port R ≃ Fin M)
    (truth : (Fin M → Bool) → Bool) (b : ℕ) :
    let g := J9End.chart d anchor idx truth
    ((2:ℚ)*(L:ℚ)*2^b) * ∑ x : Fin M → Bool,
      chartWeight g b x *
        MvPolynomial.coeff β (rowCompiler (chartBase g x) (chartKernel d anchor idx truth b)) =
      J9FactorBounds.firstCoeff g b := by
  dsimp only
  let g := J9End.chart d anchor idx truth
  rw [Finset.mul_sum, J9FactorBounds.firstCoeff]
  simp only [normalized_rows_one_assignment]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum, Int.cast_mul, Int.cast_sum, div_mul_eq_mul_div]

#print axioms chartOther_factor
#print axioms normalized_rows_one_assignment
#print axioms normalized_rows_full_cube
end
end J9LayoutTransfer

