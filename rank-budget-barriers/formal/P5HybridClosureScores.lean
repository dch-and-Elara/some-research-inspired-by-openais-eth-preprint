import P5HybridClosureConditional

/-! Exact likelihood scores for a partial fixing of the *shared primitive
addresses*. These sums can be evaluated in the manuscript's small
support enumeration, not by traversing all source labelings. -/
namespace Paper5.HybridClosure
open scoped BigOperators Classical
open GuardExpectation
open J1MainSourceCollision J1MainSourceLabels
open J6R11CollisionGreedy (equalityMass average_eq_indicator uniform_product_mean)

variable {V F B I S E : Type*} [Fintype V] [Fintype F] [Fintype B]
  [Fintype I] [DecidableEq I] [Fintype S] [Nonempty S] [Fintype E]

private theorem average_subtract_constant {X A : Type*} [Fintype X] [DecidableEq X] [Fintype A]
    (w : X→A→ℚ) (hw : ∀x,∑a,w x a=1) (f : (X→A)→ℚ) (c : ℚ) :
    average w (fun z=>f z-c)=average w f-c := by
  have h := average_const w hw c
  unfold average at h ⊢
  simp only [mul_sub,Finset.sum_sub_distrib]
  rw [h]

noncomputable def incidenceConditional (t : I) (tie : F→Option B) (var : E→V) (fac : E→F)
    (w : Primitive V F B I→S→ℚ) : ℚ :=
  ∑ p : E×E, (average (fun i : pairSupport t tie var fac p.1 p.2=>w i)
      (fun z=>J1MainSourceCollision.indicator (pairProjection t tie var fac p.1 p.2 z false=
        pairProjection t tie var fac p.1 p.2 z true)) -
      1/(Fintype.card (DiagonalAbundance.Draw I S):ℚ))

theorem incidence_conditional_exact (t : I) (tie : F→Option B)
    (var : E→V) (fac : E→F) (w : Primitive V F B I→S→ℚ) (hw : ∀ i,∑a,w i a=1) :
    average w (incidenceCost t tie var fac)=incidenceConditional t tie var fac w := by
  unfold incidenceCost
  simp_rw [deviation_eq_pairs]
  rw [average_sum]
  unfold incidenceConditional
  apply Finset.sum_congr rfl
  intro p _
  rw [average_subtract_constant _ hw,conditional_actual_pair t tie var fac p.1 p.2 w hw]

noncomputable def variableConditional
    (w : Primitive V F B I→S→ℚ) : ℚ :=
  ∑ j : I, ∑ pq : V×V, (equalityMass w (.inl (pq.1,j)) (.inl (pq.2,j)) -
    1/(Fintype.card S:ℚ))

private theorem average_decidable_irrel {X A : Type*} [Fintype X] [Fintype A]
    (d₀ d₁ : DecidableEq X) (w : X→A→ℚ) (f : (X→A)→ℚ) :
    @average X A _ d₀ _ w f = @average X A _ d₁ _ w f := by
  rw [Subsingleton.elim d₀ d₁]

theorem variable_conditional_exact
    (w : Primitive V F B I→S→ℚ) (hw : ∀ i,∑a,w i a=1) :
    average w variableCost=variableConditional w := by
  unfold variableCost variableConditional
  rw [average_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp_rw [deviation_eq_pairs]
  rw [average_sum]
  apply Finset.sum_congr rfl
  intro pq _
  rw [average_subtract_constant _ hw]
  congr 1
  have h := average_eq_indicator w hw (.inl (pq.1,j)) (.inl (pq.2,j))
  exact (average_decidable_irrel inferInstance (Classical.decEq _) w _).trans h

theorem conditional_scores (t : I) (tie : F→Option B) (var : E→V) (fac : E→F)
    (p q : ℚ) (w : Primitive V F B I→S→ℚ) (hw : ∀ i,∑a,w i a=1) :
    average w (fun z => p*incidenceCost t tie var fac z + q*variableCost z) =
      p*incidenceConditional t tie var fac w + q*variableConditional w := by
  rw [average_add,average_mulConst,average_mulConst,incidence_conditional_exact _ _ _ _ _ hw,
    variable_conditional_exact _ hw]

theorem good_conditioned_layout (t : I) (tie : F→Option B) (var : E→V) (fac : E→F)
    [DecidableEq S] (p q : ℚ) :
    ∃ z : Primitive V F B I→S,
      p*incidenceCost t tie var fac z+q*variableCost z ≤
        DiagonalAbundance.mean (fun (z : Primitive V F B I→S)=>p*incidenceCost t tie var fac z+q*variableCost z) := by
  let w : Primitive V F B I→S→ℚ := fun _ _=>(Fintype.card S:ℚ)⁻¹
  have h0 : ∀ i a,0≤w i a := by intro i a; dsimp [w]; positivity
  have h1 : ∀ i,∑ a,w i a=1 := by intro i; simp [w,nsmul_eq_mul]
  let score := fun (z : Primitive V F B I→S) => p*incidenceCost t tie var fac z+q*variableCost z
  obtain ⟨z,hz⟩ := exists_sample_by_conditioning w h0 h1 score
  change score z≤average (fun _ _=>(Fintype.card S:ℚ)⁻¹) score at hz
  rw [uniform_product_mean] at hz
  exact ⟨z,hz⟩

omit [Fintype V] [Fintype F] [Fintype B] in
theorem conditioned_incidence_samples (t : I) (tie : F→Option B) (var : E→V) (fac : E→F) :
    (∑ p : E×E, Fintype.card (pairSupport t tie var fac p.1 p.2→S)) ≤
      (Fintype.card E)^2*((Fintype.card S)^(2*Fintype.card I))^2 := by
  calc
    _ ≤ ∑ _ : E×E, ((Fintype.card S)^(2*Fintype.card I))^2 :=
      Finset.sum_le_sum (fun p _=> conditional_pair_enumeration_size t tie var fac p.1 p.2 Fintype.card_pos)
    _ = _ := by simp [Fintype.card_prod,pow_two]

#print axioms incidence_conditional_exact
#print axioms variable_conditional_exact
#print axioms conditional_scores
#print axioms good_conditioned_layout
#print axioms conditioned_incidence_samples
end Paper5.HybridClosure