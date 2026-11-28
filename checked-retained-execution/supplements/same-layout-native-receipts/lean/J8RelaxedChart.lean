import J8RelaxedFusion
import J9R13ChartFirst
set_option warningAsError true
set_option linter.unusedSectionVars false
namespace J8Physical.Relaxed
open scoped BigOperators Classical Polynomial
open Polynomial LiteralPortCompiler J8EndToEnd J8J9Grouped
open J9LayoutTransfer J9R13PhysicalFusion J9R13PhysicalTables J9R13GroupFusion J9R13ChartFirst
open DyadicProbeCompiler
noncomputable section
local instance (priority := 10000) relaxedChartFinDecEq (n : ℕ) : DecidableEq (Fin n) :=
  fun i j => Classical.propDecidable (i=j)
variable {Packet R S V G : Type*} {P : V→Type*} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]
def argument (e : RowEndpointSeating d) (even : Even L) (g : G)
    (x : (LocalPin d g → Bool) × LocalBits d g) (r : LocalRow d g) (leg : Bool) : ℤ :=
  ((localHit d e even r).map fun p =>
    if p.1 = leg then J9FactorBounds.kernel L * bit (x.2 p.2.1 p.2.2) else 0).getD 0

theorem argument_cast (e : RowEndpointSeating d) (even : Even L) (tail : IntegralArguments d)
    (g : G) (x : (LocalPin d g → Bool) × LocalBits d g) (r : LocalRow d g) (leg : Bool) :
    (argument d e even g x r leg : Source) =
      (physicalBase d e even (J9FactorBounds.kernel L) tail g x r leg).coeff 0 := by
  simp only [argument, physicalBase, Polynomial.coeff_add, Polynomial.coeff_C_zero,
    Polynomial.mul_coeff_zero, Polynomial.coeff_X_zero, zero_mul, add_zero]
  cases hh : localHit d e even r with
  | none => simp
  | some p =>
    by_cases h : p.1 = leg <;> simp [h, bit_cast]

theorem argument_eq_chart (e : RowEndpointSeating d) (even : Even L) (a : S)
    (idx : Wire R ≃ Fin M) (truth : (Fin M → Bool) → Bool) (x : Cube d)
    (g : G) (r : LocalRow d g) (leg : Bool) :
    let c := J9End.chart d a idx truth
    argument d e even g (x g) r leg =
      J9FactorBounds.arg (J9FactorBounds.kernel L) (c.hit r.1 leg)
        (cubeEquiv d idx x (c.rowInput r.1 leg)) := by
  dsimp only
  change _ = J9FactorBounds.arg (J9FactorBounds.kernel L)
    (J9End.hit d (r.1,leg)) (cubeEquiv d idx x (idx (J9End.hitDestination d a (r.1,leg))))
  unfold argument
  cases hh : localHit d e even r with
  | none =>
    have hzero : J9End.hit d (r.1,leg) = false := by
      cases h : J9End.hit d (r.1,leg)
      · rfl
      · obtain ⟨y,hy⟩ := (J9End.hit_true_iff d _).1 h
        have bad := localHit_complete d e even r hy
        rw [hh] at bad
        cases bad
    simp [hzero, J9FactorBounds.arg]
  | some p =>
    by_cases hleg : p.1 = leg
    · have h := localHit_sound d e even r hh
      rw [hleg] at h
      have hs := (J9End.hit_true_iff d (r.1,leg)).2 ⟨_,h⟩
      have hbit := congrArg (fun q : Assignment d g => q.2 p.2.1 p.2.2)
        (cubeLabels_local d x g)
      change cubeLabels d x (recoverWire d p.2) = _ at hbit
      have hglob : cubeEquiv d idx x (idx (J9End.hitDestination d a (r.1,leg))) =
          (x g).2 p.2.1 p.2.2 := by
        rw [J9End.hitDestination_spec d a h]
        simpa only [cubeEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply] using hbit
      simp [hleg, hs, hglob, J9FactorBounds.arg, bit]
    · have hzero : J9End.hit d (r.1,leg) = false := by
        cases h : J9End.hit d (r.1,leg)
        · rfl
        · obtain ⟨y,hy⟩ := (J9End.hit_true_iff d _).1 h
          have bad := localHit_complete d e even r hy
          rw [hh, Option.map_some, Option.some.injEq] at bad
          exact (hleg (congrArg Prod.fst bad)).elim
      simp [hleg, hzero, J9FactorBounds.arg]

theorem baseline_chart (e : RowEndpointSeating d) (even : Even L) (a : S) (idx : Wire R≃Fin M)
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
theorem compiled_constant_on_chart
    (e : RowEndpointSeating d) (even : Even L) (hL : 2 < L)
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
    (e : RowEndpointSeating d) (even : Even L) (hL : 2 < L)
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
#print axioms compiled_constant_on_chart
#print axioms exactFirst_from_seated_children
end
end J8Physical.Relaxed