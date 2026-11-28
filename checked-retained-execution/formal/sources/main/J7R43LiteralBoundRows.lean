import J8J9GroupedRange
import J6R15SpecializedBoxNativeBase

/-! Uniform magnitude bound from actual endpoint hits. Both padding and
the local scope are respected: an unmatched subdivision contributes one. -/
namespace J7R43Literal
open scoped BigOperators Classical Polynomial
open J8Physical J8J9Grouped J6R14SpecializedBox
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

variable {Packet R S V G : Type} {P : V→Type} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]
variable (e : EndpointSeating d) (even : Even L)

def exactBaselineRow (g : G) (x : Assignment d g) (r : LocalRow d g) : ℤ :=
  J8SourceMoment.rowFactor none (argument d e even g x r false) (argument d e even g x r true)

theorem baselineRow_chart (s : S) (idx : Wire R ≃ Fin M) (x : Cube d) (g : G) (r : LocalRow d g) :
    let c := J9End.chart d s idx (fun _ => true)
    exactBaselineRow d e even g (x g) r =
      J9FactorBounds.rowBase (J9FactorBounds.kernel L) (c.hit r.val)
        (fun leg => cubeEquiv d idx x (c.rowInput r.val leg)) := by
  dsimp only
  unfold exactBaselineRow J9FactorBounds.rowBase
  rw [argument_eq_chart d e even s idx (fun _ => true) x g r false,
    argument_eq_chart d e even s idx (fun _ => true) x g r true]
  simp only [J8SourceMoment.rowFactor, Option.elim_none, J8SourceMoment.oldEquality_eq,
    TargetDerivative.equality,J9FactorBounds.equalityPoly]
  ring

private theorem chart_positive {Z : Type*} (c : J9FactorBounds.Chart L M R Z)
    (x : Fin M→Bool) (oneHit : ∀ r, ¬ (c.hit r false=true ∧ c.hit r true=true)) (r : R) :
    1 ≤ J9FactorBounds.rowBase (J9FactorBounds.kernel L) (c.hit r)
      (fun leg => x (c.rowInput r leg)) := by
  rcases J9FactorBounds.rowBase_cases _ _ (fun leg => x (c.rowInput r leg)) (oneHit r) with h|h
  · rw [h]
  · rw [h]
    have h0 := J9FactorBounds.kernel_nonpos L
    omega

set_option maxHeartbeats 3000000 in
theorem literal_group_row_bounds (s : S) (idx : Wire R ≃ Fin M) (hL : 1≤L)
    (capacity : L*Fintype.card Packet ≤ 3*M) (g : G) (x : Assignment d g) :
    (∀ r : LocalRow d g, 1≤exactBaselineRow d e even g x r) ∧
      (∏ r : LocalRow d g, exactBaselineRow d e even g x r) ≤ (2:ℤ)^(6*M) := by
  let c := J9End.chart d s idx (fun _ => true)
  let u := onlyGroup d g x
  let base (r : R) := J9FactorBounds.rowBase (J9FactorBounds.kernel L) (c.hit r)
    (fun leg => cubeEquiv d idx u (c.rowInput r leg))
  have oneHit := J9End.chart_one_hit d s idx (fun _ => true) e
  have h1 (r : R) : 1 ≤ base r := chart_positive c (cubeEquiv d idx u) oneHit r
  have hBase (r : LocalRow d g) : exactBaselineRow d e even g x r = base r.val := by
    have h := baselineRow_chart d e even s idx u g r
    simpa only [u,onlyGroup_here] using h
  constructor
  · intro r
    rw [hBase]
    exact h1 r.val
  have hActive := J9End.chart_active_rows_budget d s idx (fun _ => true) capacity
  change L * (J9FactorBounds.activeRows c).card ≤ 3*M at hActive
  let S₀ : Finset R := Finset.univ.filter (fun r => d.rowLabel r=g)
  let B₀ : Finset R := J9FactorBounds.activeRows c
  calc
    _ = ∏ r ∈ S₀, base r := by
      simp only [hBase]
      let j : LocalRow d g ≃ {r // r∈S₀} := Equiv.subtypeEquivRight (fun _ => by simp [S₀])
      exact (Fintype.prod_equiv j (fun r => base r.val) (fun r => base r.val) (fun _ => rfl)).trans
        (Finset.prod_coe_sort S₀ base)
    _ ≤ ∏ r : R, base r := by
      unfold S₀
      rw [Finset.prod_filter]
      refine Finset.prod_le_prod (fun r _ => ?_) (fun r _ => ?_)
      · split_ifs
        · exact (le_trans (by norm_num) (h1 r))
        · norm_num
      · split_ifs
        · exact le_rfl
        · exact h1 r
    _ = ∏ r ∈ B₀, base r := by
      unfold B₀ J9FactorBounds.activeRows
      rw [Finset.prod_filter]
      refine Finset.prod_congr rfl (fun r _ => ?_)
      by_cases h : (c.hit r false || c.hit r true)=true
      · simp only [if_pos h]
      · rw [if_neg h]
        cases h0 : c.hit r false <;> cases h1' : c.hit r true <;>
          simp_all [base,J9FactorBounds.rowBase,J9FactorBounds.equalityPoly,J9FactorBounds.arg]
    _ ≤ ∏ _r ∈ B₀, (2:ℤ)^(2*L) := by
      refine Finset.prod_le_prod (fun r _ => le_trans (by norm_num) (h1 r)) (fun r _ => ?_)
      have hb : 0≤base r := (show (0:ℤ)≤1 from by decide).trans (h1 r)
      have hh : |base r| ≤ 1+|J9FactorBounds.kernel L| :=
        J9FactorBounds.rowBase_abs_le (J9FactorBounds.kernel L) (J9FactorBounds.kernel_nonpos L)
          (c.hit r) (fun leg => cubeEquiv d idx u (c.rowInput r leg)) (oneHit r)
      rw [abs_of_nonneg hb] at hh
      exact hh.trans (J9FactorBounds.kernel_budget L hL)
    _ = (2:ℤ)^(2*L*B₀.card) := by
      rw [Finset.prod_const]
      exact (pow_mul (2:ℤ) (2*L) B₀.card).symm
    _ ≤ _ := by
      apply pow_le_pow_right₀ (by decide)
      change 2*L*(J9FactorBounds.activeRows c).card≤6*M
      rw [Nat.mul_assoc]
      exact (Nat.mul_le_mul_left 2 hActive).trans_eq (by ring)
#print axioms baselineRow_chart
#print axioms literal_group_row_bounds
end
end J7R43Literal