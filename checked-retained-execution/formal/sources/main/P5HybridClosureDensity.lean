import J1MainSourceCollision
import MainIncidence
import BalancedUnion

/-! From literal cell caps to norms of actual pin words, and one balanced
whole-symbol union per potentially observed coordinate. The two laws need
not be independent of one another. -/
namespace Paper5.HybridClosure
open scoped BigOperators Classical
open EmpiricalCutMoments ProductVariance

variable {V P I A : Type*}
  [Fintype V] [Nonempty V] [DecidableEq V] [Fintype P]
  [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Nonempty A]

theorem literal_load_is_fibre {X C : Type*} [Fintype X] [DecidableEq C] (cell : X→C) (c : C) :
    J1MainSourceCollision.load cell c=(SourceDensity.fiberCount cell c:ℚ) := by
  unfold J1MainSourceCollision.load J1MainSourceCollision.indicator SourceDensity.fiberCount
  rw [Finset.card_filter,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : cell a=c <;> simp [h]

omit [DecidableEq V] in
theorem main_pin_domination (pin : V↪P) (cell : P→(I→A)×(I→A))
    (H : ℕ) (hP : 2*Fintype.card P≤H*Fintype.card V)
    (hCell : ∀ c, J1MainSourceCollision.load cell c≤ 2*(Fintype.card P:ℚ)/
      (Fintype.card ((I→A)×(I→A)):ℚ)) :
    ∀ x, empiricalLaw (fun v => (cell (pin v)).2) x≤(H:ℚ)*uniformWeight (I→A) := by
  refine MainIncidence.project_marked_incidence pin cell H hP ?_ Prod.snd
    (Fintype.card (I→A)) (MainIncidence.factor_word_fiber (I:=I) (A:=A))
  intro c
  rw [←literal_load_is_fibre]
  exact hCell c

omit [DecidableEq V] in
theorem retained_pin_domination (pin : V↪P) (cell : P→(I→A)×(I→A))
    (H : ℕ) (hP : 2*Fintype.card P≤H*Fintype.card V)
    (kept : Finset I)
    (hCell : ∀ c, J1MainSourceCollision.load cell c≤ 2*(Fintype.card P:ℚ)/
      (Fintype.card ((I→A)×(I→A)):ℚ)) :
    ∀ x, empiricalLaw (fun v => SourceDensity.firstCoordinates kept (cell (pin v))) x≤
      (H:ℚ)*uniformWeight (kept→A) := by
  refine MainIncidence.project_marked_incidence pin cell H hP ?_
    (SourceDensity.firstCoordinates kept) _ (SourceDensity.ordered_cell_projection_regular kept)
  intro c
  rw [←literal_load_is_fibre]
  exact hCell c

omit [DecidableEq V] [Nonempty V] in
theorem marginal_domination (L : V→I→A) (C : ℚ)
    (hdom : ∀ x,empiricalLaw L x≤ C*uniformWeight (I→A)) (j : I) (a : A) :
    empiricalLaw (fun v => L v j) a ≤ C/(Fintype.card A:ℚ) := by
  let f := fun x : A => if x=a then (1:ℚ) else 0
  have hw (g : (I→A)→ℚ) :
      (∑ x,uniformWeight (I→A)*g x)=uniformMean g := Finset.mul_sum _ _ _ |>.symm
  calc
    _ = ∑ x : I→A,empiricalLaw L x*f (x j) := by
      rw [empirical_expectation]
      unfold empiricalLaw
      congr 1
      rw [Finset.card_filter,Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro v _
      by_cases h : L v j=a <;> simp [f,h]
    _ ≤ ∑ x : I→A,(C*uniformWeight (I→A))*f (x j) := by
      apply Finset.sum_le_sum
      intro x _
      exact mul_le_mul_of_nonneg_right (hdom x) (by unfold f; split <;> norm_num)
    _ = C*uniformMean (fun x : I→A => f (x j)) := by
      simp_rw [mul_assoc]
      rw [←Finset.mul_sum,hw]
    _ = _ := by
      rw [coordinate_mean j f]
      unfold uniformMean f
      simp [uniformWeight,div_eq_mul_inv]

omit [DecidableEq V] in
theorem choose_balanced_symbols (L : V→I→A) (C : ℚ)
    (hdom : ∀ x,empiricalLaw L x≤C*uniformWeight (I→A))
    (hC : C/(Fintype.card A:ℚ)≤3/4) :
    ∃ u : I→Finset A, ∀ j,
      (1/4:ℚ)*Fintype.card V ≤
        (min (labelCut L id u j).card (Fintype.card V-(labelCut L id u j).card):ℕ) := by
  have he (j : I) := BalancedUnion.exists_balanced_vertex_union_of_law (fun v => L v j)
    (fun a => (marginal_domination L C hdom j a).trans hC)
  choose s hs using he
  refine ⟨s,fun j => ?_⟩
  simpa only [labelCut,BalancedUnion.vertexUnion,id_eq] using hs j

#print axioms literal_load_is_fibre
#print axioms main_pin_domination
#print axioms retained_pin_domination
#print axioms marginal_domination
#print axioms choose_balanced_symbols
end Paper5.HybridClosure