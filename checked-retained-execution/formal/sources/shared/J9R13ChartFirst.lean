import J9R13PhysicalFusion
import J9LayoutTransferSource
import J8J9GroupedRows

/-!
# Actual J8 child product supplies the J9 chart's exactFirst

At zero, the physical row argument agrees with the integer Cauchy
chart, and the source feature is its actual tile moment. Grouped
target ports are reindexed bijectively to the original row legs
using the seating law, not an assumed global coefficient match.
-/

namespace J9R13ChartFirst
open scoped BigOperators Classical Polynomial
open LiteralPortCompiler J8Physical J8EndToEnd J8J9Grouped
open J9LayoutTransfer J9R13PhysicalFusion J9R13PhysicalTables J9R13GroupFusion
open DyadicProbeCompiler

noncomputable section
-- Match the generic compiler's proof-time equality choice on its left cube.
local instance (priority := 10000) literalFinDecEq (n : ℕ) : DecidableEq (Fin n) :=
  fun i j => Classical.propDecidable (i=j)

variable {Packet R S V G : Type*} {P : V→Type*} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]

def atZero : Source[X]→+*ℚ := rationalMap.comp (Polynomial.evalRingHom 0)

theorem atZero_coeff (q : Source[X]) : atZero q=rationalMap (q.coeff 0) := by
  change rationalMap (q.eval 0) = _
  rw [Polynomial.coeff_zero_eq_eval_zero]

set_option linter.unusedSectionVars false in
theorem baseline_chart (e : EndpointSeating d) (even : Even L) (a : S) (idx : Wire R≃Fin M)
    (tail : IntegralArguments d) (truth : (Fin M→Bool)→Bool) (x : Fin M→Bool) (p : Port R) :
    atZero (baseline d e even idx tail x p) =
      chartBase (J9End.chart d a idx truth) x p := by
  let c := (cubeEquiv d idx).symm x
  let g := d.rowLabel p.1
  let r : LocalRow d g := ⟨p.1,rfl⟩
  rw [atZero_coeff]
  change rationalMap ((physicalBase d e even (J9FactorBounds.kernel L) tail g (c g) r p.2).coeff 0) = _
  rw [← argument_cast, map_intCast]
  have H := argument_eq_chart d e even a idx truth c g r p.2
  dsimp only at H
  change argument d e even g (c g) r p.2 =
    J9FactorBounds.arg (J9FactorBounds.kernel L) ((J9End.chart d a idx truth).hit p.1 p.2)
      (cubeEquiv d idx c ((J9End.chart d a idx truth).rowInput p.1 p.2)) at H
  rw [show cubeEquiv d idx c=x from Equiv.apply_symm_apply _ _] at H
  rw [H]
  rfl

set_option linter.unusedSectionVars false in
theorem feature_chart (a : S) (idx : Wire R≃Fin M) (b : Fin (Fintype.card (PinTile d a)))
    (truth : (Fin M→Bool)→Bool) (x : Fin M→Bool) :
    atZero (featureValue d a idx b x) = (J9FactorBounds.moment (J9End.chart d a idx truth) b x : ℚ) := by
  rw [atZero_coeff]
  unfold featureValue
  rw [Polynomial.coeff_C_zero,← feature_cast,map_intCast,cubeFeature_eq d a b idx truth]
  rw [Equiv.apply_symm_apply]

def wireOf {a : S} (j : TargetPorts d a) : Port R := (j.1.1,j.2)

omit [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
  [(v : V) → Fintype (P v)] in
theorem wireOf_injective (a : S) : Function.Injective (wireOf d (a:=a)) := by
  intro j k h
  apply Prod.ext
  · exact Subtype.ext (congrArg (fun p : Port R => p.1) h)
  · exact congrArg (fun p : Port R => p.2) h

set_option linter.unusedSectionVars false in
theorem crossing_chart (a : S) (off : d.rowLabel (pinWire d a).1 ≠ d.pinLabel a)
    (even : Even L) (hL : 2 < L) (idx : Wire R≃Fin M) (b : Fin (Fintype.card (PinTile d a)))
    (kt : TargetPorts d a→Source[X]) (truth : (Fin M→Bool)→Bool) (p : Port R) :
    atZero (crossing d even hL a b kt p) = chartKernel d a idx truth b p := by
  rw [chartKernel]
  by_cases hp : p ∈ targets d (pinWire d a)
  · have hG := target_has_one_target_group d hp (pinWire_is_target d a off)
    let j : TargetPorts d a := (⟨p.1,hG⟩,p.2)
    have hj : j∈groupedTargets d a := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩
    have hs : crossing d even hL a b kt p = physicalKernel d a even hL (J9FactorBounds.kernel L) b kt j := by
      unfold crossing targetKernel
      rw [Finset.sum_eq_single_of_mem j hj]
      · rw [if_pos rfl]
      · intro j' _ hj'
        have hn : ((j'.1.1,j'.2) : Port R) ≠ p := by
          intro hw
          exact hj' (wireOf_injective d a (hw.trans (show p=wireOf d j from rfl)))
        exact if_neg hn
    rw [hs,if_pos hp,atZero_coeff,constructed_kernel_normalized d a even hL _ _ _ j hj]
    have hden :
      (physicalDenominator d a j)^(b.val+1) =
        (J9FactorBounds.denominator (J9End.chart d a idx truth) b (J9End.slot d p) : ℚ) := by
      unfold J9FactorBounds.denominator physicalDenominator
      push_cast
      rfl
    rw [hden]
  · rw [if_neg hp]
    unfold crossing targetKernel
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j hj
    have hn : ((j.1.1,j.2) : Port R) ≠ p := by
      intro he
      exact hp (he ▸ (Finset.mem_filter.mp hj).2)
    rw [if_neg hn,map_zero]

set_option linter.unusedSectionVars false in
theorem compiled_constant_on_chart
    (e : EndpointSeating d) (even : Even L) (hL : 2 < L)
    (a : S) (off : d.rowLabel (pinWire d a).1 ≠ d.pinLabel a)
    (idx : Wire R ≃ Fin M) (F : OldTables d) (sign : S→Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) (kt : TargetPorts d a→Source[X]) :
    let t := satisfied (globalCNF d idx F sign)
    let g := J9End.chart d a idx t
    rationalMap ((MvPolynomial.coeff β (completed (literalSystem d idx F sign)
      (literalBase d e even a idx tail b) (literalKernel d (M:=M) even hL a b kt))).coeff 0) =
      ∑ x : Fin M→Bool, chartWeight g b x *
        MvPolynomial.coeff β (rowCompiler (chartBase g x) (chartKernel d a idx t b)) := by
  dsimp only
  unfold literalSystem literalBase literalKernel
  rw [← atZero_coeff,J9R13Compiler.singleton_separate,map_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp only [map_mul,map_truth,feature_chart d a idx b (satisfied (globalCNF d idx F sign))]
  have H : atZero (MvPolynomial.coeff β
      (rowCompiler (baseline d e even idx tail x) (crossing d even hL a b kt))) =
      MvPolynomial.coeff β (rowCompiler (chartBase (J9End.chart d a idx
        (satisfied (globalCNF d idx F sign))) x) (chartKernel d a idx
          (satisfied (globalCNF d idx F sign)) b)) := by
    unfold rowCompiler
    rw [reduce_completed]
    simp only [baseline_chart d e even a idx tail (satisfied (globalCNF d idx F sign)),
      crossing_chart d a off even hL idx b kt (satisfied (globalCNF d idx F sign))]
  rw [H]
  rfl

set_option linter.unusedSectionVars false in
theorem exactFirst_from_seated_children
    (e : EndpointSeating d) (even : Even L) (hL : 2 < L)
    (a : S) (off : d.rowLabel (pinWire d a).1 ≠ d.pinLabel a)
    (idx : Wire R ≃ Fin M) (F : OldTables d) (sign : S→Bool) (tail : IntegralArguments d)
    (b : Fin (Fintype.card (PinTile d a))) (kt : TargetPorts d a→Source[X])
    (k : ℕ) (hpow : L=2^k)
    (rowTail : (Fin M→Bool)→R→Bool→ℚ[X]) (crossTail : Fin L→ℚ[X]) (srcTail : (Fin M→Bool)→ℚ[X]) :
    (2:ℚ)^(k+1+b.val) * rationalMap ((MvPolynomial.coeff β (completed (literalSystem d idx F sign)
      (literalBase d e even a idx tail b) (literalKernel d (M:=M) even hL a b kt))).coeff 0) =
      (J9End.literalCompleted (J9End.chart d a idx (satisfied (globalCNF d idx F sign)))
        b rowTail crossTail srcTail).coeff 1 := by
  rw [compiled_constant_on_chart d e even hL a off, J9End.literal_first_exact]
  have h : (L:ℚ)=2^k := by exact_mod_cast hpow
  have hscale : (2:ℚ) * L * 2^b.val = 2^(k+1+b.val) := by rw [h,pow_add,pow_add]; ring
  rw [← hscale]
  have H := normalized_rows_full_cube d a idx (satisfied (globalCNF d idx F sign)) b
  dsimp only at H
  convert H using 1
  congr! 4

#print axioms baseline_chart
#print axioms feature_chart
#print axioms wireOf_injective
#print axioms crossing_chart
#print axioms compiled_constant_on_chart
#print axioms exactFirst_from_seated_children

end
end J9R13ChartFirst
