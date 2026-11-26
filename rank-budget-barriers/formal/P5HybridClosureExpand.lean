import P5HybridClosureGraph

/-! Exact finite triangle-replacement expansion transfer, using the same
graph as the cloned formula and its two group operands. -/
namespace Paper5.HybridClosure
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

def cutSign {U : Type*} [DecidableEq U] (S : Finset U) (x : U) : Bool := decide (x∈S)

def disagree (b c : Bool) : ℕ := if b=c then 0 else 1

def vote (b : Fin 3→Bool) : Bool := (b 0 && b 1) || (b 0 && b 2) || (b 1 && b 2)

def voteCut (S : Finset (TriVertex V)) : Finset V :=
  Finset.univ.filter (fun v => vote (fun i => cutSign S (v,i))=true)

theorem voteCut_sign (S : Finset (TriVertex V)) (v : V) :
    cutSign (voteCut S) v = vote (fun i => cutSign S (v,i)) := by
  simp [cutSign,voteCut]

def roundingErrors (S : Finset (TriVertex V)) : ℕ :=
  ∑ p, disagree (cutSign S p) (cutSign (voteCut S) p.1)

theorem boundary_disagree {U : Type*} [DecidableEq U] (F : Finset (U×U)) (S : Finset U) :
    (GraphCutMoments.boundary F S).card = ∑ e∈F,disagree (cutSign S e.1) (cutSign S e.2) := by
  unfold GraphCutMoments.boundary
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h₁:e.1∈S <;> by_cases h₂:e.2∈S <;> simp [cutSign,disagree,h₁,h₂]

private theorem triangle_vote_count :
    ∀ b : Fin 3→Bool, (∑ i,disagree (b i) (b (i+1))) =
      2*(∑ i,disagree (b i) (vote b)) := by decide

theorem inner_boundary_twice_rounding (S : Finset (TriVertex V)) :
    (GraphCutMoments.boundary (innerEdges V) S).card = 2*roundingErrors S := by
  rw [boundary_disagree,innerEdges,Finset.sum_image (fun _ _ _ _ h => innerEdge_injective h)]
  unfold roundingErrors
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  change (∑ i : Fin 3,disagree (cutSign S (v,i)) (cutSign S (v,i+1))) =
    2 * ∑ i : Fin 3,disagree (cutSign S (v,i)) (cutSign (voteCut S) v)
  rw [voteCut_sign]
  exact triangle_vote_count _

private theorem cut_change_bound :
    ∀ x y x' y' : Bool, disagree x' y' ≤ disagree x y + (disagree x x'+disagree y y') := by decide

theorem base_boundary_le_outer_plus_rounding (E : Finset (V×V))
    (cubic : ∀ v,GraphCutMoments.degree E v=3) (S : Finset (TriVertex V)) :
    (GraphCutMoments.boundary E (voteCut S)).card ≤
      (GraphCutMoments.boundary (outerEdges E cubic) S).card+roundingErrors S := by
  let f := fun p : TriVertex V => disagree (cutSign S p) (cutSign (voteCut S) p.1)
  rw [boundary_disagree,boundary_disagree]
  change _ ≤ _+∑ p,f p
  rw [←outer_weight_sum E cubic f,←Finset.sum_add_distrib]
  unfold outerEdges
  rw [Finset.sum_image (fun _ _ _ _ h => outerEdge_injective E cubic h)]
  rw [←Finset.sum_attach E]
  apply Finset.sum_le_sum
  intro e _
  change disagree (cutSign (voteCut S) e.1.1) (cutSign (voteCut S) e.1.2) ≤
    disagree (cutSign S (exteriorPort E cubic (e,false)))
      (cutSign S (exteriorPort E cubic (e,true))) +
      (f (exteriorPort E cubic (e,false)) + f (exteriorPort E cubic (e,true)))
  unfold f
  rw [exteriorPort_left_base,exteriorPort_right_base]
  exact cut_change_bound _ _ _ _

def bitCount (b : Bool) : ℕ := if b then 1 else 0

private theorem bitCount_error :
    ∀ a b : Bool, bitCount a ≤ bitCount b+disagree a b := by decide

private theorem bitCount_complement_error :
    ∀ a b : Bool, bitCount (!a) ≤ bitCount (!b)+disagree a b := by decide

theorem sum_of_sign {U : Type*} [Fintype U] [DecidableEq U] (S : Finset U) :
    (∑ p,bitCount (cutSign S p))=S.card := by simp [bitCount,cutSign]

theorem sum_of_complement_sign {U : Type*} [Fintype U] [DecidableEq U] (S : Finset U) :
    (∑ p,bitCount (!cutSign S p))=Fintype.card U-S.card := by
  have h : (∑ p,bitCount (!cutSign S p))=((Finset.univ : Finset U)\S).card := by
    rw [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ]
    have he : (∑ p, bitCount (!cutSign S p)) + (∑ p, bitCount (cutSign S p)) = Fintype.card U := by
      rw [←Finset.sum_add_distrib]
      have hbit : ∀ b : Bool, bitCount (!b)+bitCount b=1 := by decide
      simp [hbit]
    rw [sum_of_sign] at he
    omega
  rw [h,Finset.card_sdiff,Finset.inter_univ,Finset.card_univ]

omit [DecidableEq V] in
private theorem sum_of_lifted_sign (g : V→Bool) :
    (∑ p : TriVertex V,bitCount (g p.1))=3*(∑ v,bitCount (g v)) := by
  rw [Fintype.sum_prod_type,Finset.mul_sum]
  simp

theorem smaller_side_rounding (S : Finset (TriVertex V)) :
    min S.card (Fintype.card (TriVertex V)-S.card) ≤
      3*min (voteCut S).card (Fintype.card V-(voteCut S).card)+roundingErrors S := by
  have h₁ := Finset.sum_le_sum (s:=(Finset.univ : Finset (TriVertex V)))
    (fun p _ => bitCount_error (cutSign S p) (cutSign (voteCut S) p.1))
  rw [Finset.sum_add_distrib,sum_of_sign,sum_of_lifted_sign,sum_of_sign] at h₁
  have h₂ := Finset.sum_le_sum (s:=(Finset.univ : Finset (TriVertex V)))
    (fun p _ => bitCount_complement_error (cutSign S p) (cutSign (voteCut S) p.1))
  rw [Finset.sum_add_distrib,sum_of_complement_sign,
    sum_of_lifted_sign (fun v => !cutSign (voteCut S) v),sum_of_complement_sign] at h₂
  by_cases h : (voteCut S).card ≤ Fintype.card V-(voteCut S).card
  · rw [min_eq_left h]
    exact (min_le_left _ _).trans h₁
  · rw [min_eq_right (Nat.le_of_not_ge h)]
    exact (min_le_right _ _).trans h₂

/-- A supplied simple cubic base expander gives the actual replacement
expansion γ/3 on *every* cut.  This does not assume the conclusion. -/
theorem replacement_expansion (E : Finset (V×V))
    (cubic : ∀v,GraphCutMoments.degree E v=3) (loopless : ∀v,(v,v)∉E)
    (γ : ℚ) (hγ₀ : 0≤γ) (hγ₃ : γ≤3)
    (expand : ∀ T : Finset V, γ*(min T.card (Fintype.card V-T.card) : ℕ) ≤
      ((GraphCutMoments.boundary E T).card : ℚ)) (S : Finset (TriVertex V)) :
    (γ/3)*(min S.card (Fintype.card (TriVertex V)-S.card) : ℕ) ≤
      ((GraphCutMoments.boundary (replacedEdges E cubic) S).card : ℚ) := by
  let p := roundingErrors S
  let q := min S.card (Fintype.card (TriVertex V)-S.card)
  let z := min (voteCut S).card (Fintype.card V-(voteCut S).card)
  let o := (GraphCutMoments.boundary (outerEdges E cubic) S).card
  have hRound : (q:ℚ) ≤ 3*(z:ℚ)+(p:ℚ) := by exact_mod_cast smaller_side_rounding S
  have hCross : ((GraphCutMoments.boundary E (voteCut S)).card:ℚ) ≤ (o:ℚ)+(p:ℚ) := by
    exact_mod_cast base_boundary_le_outer_plus_rounding E cubic S
  have hBase : γ*(z:ℚ) ≤ (o:ℚ)+(p:ℚ) := (expand (voteCut S)).trans hCross
  have hSplit : (GraphCutMoments.boundary (replacedEdges E cubic) S).card = 2*p+o := by
    rw [boundary_disagree,replacedEdges,Finset.sum_union (triangle_split_disjoint E cubic loopless),
      ←boundary_disagree,←boundary_disagree,inner_boundary_twice_rounding]
  have hγ := mul_le_mul_of_nonneg_left hRound (show 0≤γ/3 by positivity)
  have hP := mul_nonneg (show 0≤1-γ/3 by linarith only [hγ₃]) (show 0≤(p:ℚ) by positivity)
  change (γ/3)*(q:ℚ) ≤ _
  rw [hSplit,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  nlinarith only [hγ,hP,hBase]

#print axioms boundary_disagree
#print axioms inner_boundary_twice_rounding
#print axioms base_boundary_le_outer_plus_rounding
#print axioms smaller_side_rounding
#print axioms replacement_expansion
end Paper5.HybridClosure