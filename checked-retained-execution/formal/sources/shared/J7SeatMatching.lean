import J7FullWordLaw

/-! # Simultaneous graph-only matching by finite independent fair marks -/

open scoped BigOperators Classical
open J7SourceConditioning J7FullWordLaw

namespace J7SeatMatching
noncomputable section
set_option maxHeartbeats 1500000

variable {E U V C : Type*} [Fintype E]

def nearby (r : E → U) (c : E → V) (e : E) : Finset E :=
  Finset.univ.filter fun f => r e = r f ∨ c e = c f

theorem mem_nearby (r : E → U) (c : E → V) (e f : E) :
    f ∈ nearby r c e ↔ r e = r f ∨ c e = c f := by simp [nearby]

theorem self_near (r : E → U) (c : E → V) (e : E) : e ∈ nearby r c e :=
  (mem_nearby r c e e).2 (Or.inl rfl)

def chosen (r : E → U) (c : E → V) (z : E → Bool) (e : E) : Prop :=
  ∀ i ∈ nearby r c e, z i = if i = e then true else false

theorem chosen_matching (r : E → U) (c : E → V) (z : E → Bool) :
    Set.InjOn r {e | chosen r c z e} ∧ Set.InjOn c {e | chosen r c z e} := by
  have noConflict (e f : E) (he : chosen r c z e) (hf : chosen r c z f)
      (h : r e = r f ∨ c e = c f) : e = f := by
    classical
    by_contra ne
    have hz0 := he f ((mem_nearby r c e f).2 h)
    have hz1 := hf f (self_near r c f)
    have hne : f ≠ e := fun hk => ne hk.symm
    simp [hne] at hz0
    simp at hz1
    exact Bool.noConfusion (hz0.symm.trans hz1)
  exact ⟨fun e he f hf h => noConflict e f he hf (Or.inl h),
      fun e he f hf h => noConflict e f he hf (Or.inr h)⟩

def markedCell (r : E → U) (c : E → V) (label : E → C) (e : E) (z : E → Bool) : Option C :=
  if chosen r c z e then some (label e) else none

def fair (_ : E) (x : Bool) : ℚ := uniform Bool x

omit [Fintype E] in
theorem fair_half (e : E) (x : Bool) : fair e x = 1/2 := by simp [fair, uniform]

omit [Fintype E] in
theorem fair_norm (e : E) : (∑ x, fair e x) = 1 := uniform_normalized

omit [Fintype E] in
theorem fair_nonneg (e : E) (x : Bool) : 0 ≤ fair e x := uniform_nonneg x

theorem mean_survival (r : E → U) (c : E → V) (label : E → C) (e : E) (i : C) :
    meanCell (productWeight fair) (markedCell r c label) e (some i) =
      if label e = i then (1/2 : ℚ) ^ (nearby r c e).card else 0 := by
  classical
  let x := fun j : E => if j = e then true else false
  let v := fun j : E => fun b : Bool => if j ∈ nearby r c e then indicator b (x j) else 1
  by_cases h : label e = i
  · rw [if_pos h]
    have hmark (z : E → Bool) : indicator (markedCell r c label e z) (some i) = ∏ j : E, v j (z j) := by
      by_cases hz : chosen r c z e
      · simp only [markedCell, hz, if_true, h, indicator]
        symm
        refine Finset.prod_eq_one fun j _ => ?_
        by_cases hj : j ∈ nearby r c e
        · simp [v, x, hj, hz j hj, indicator]
        · simp [v, hj]
      · have hz' : ∃ j ∈ nearby r c e, z j ≠ x j := by
          by_contra nh
          apply hz
          intro j hj
          exact not_not.mp (fun ne => nh ⟨j,hj,ne⟩)
        obtain ⟨j,hj,hzj⟩ := hz'
        have hvj : v j (z j) = 0 := by simp [v, hj, indicator, hzj]
        rw [Finset.prod_eq_zero (Finset.mem_univ j) hvj]
        simp [markedCell,hz,indicator]
    unfold meanCell expect
    simp_rw [hmark, productWeight, ← Finset.prod_mul_distrib]
    have hp := (Fintype.prod_sum (fun (j : E) (b : Bool) => fair j b * v j b)).symm
    refine hp.trans ?_
    have hsingle (j : E) : (∑ b : Bool, fair j b * v j b) =
      if j ∈ nearby r c e then 1/2 else 1 := by
      by_cases hj : j ∈ nearby r c e
      · simp only [v, hj, if_true]
        exact (expect_indicator (fair j) (x j)).trans (fair_half _ _)
      · simp only [v, hj, if_false, mul_one]
        exact fair_norm j
    simp only [hsingle]
    rw [Finset.prod_ite]
    simp [Finset.filter_mem_eq_inter]
  · rw [if_neg h]
    have hh (z : E → Bool) : indicator (markedCell r c label e z) (some i) = 0 := by
      by_cases hz : chosen r c z e <;> simp [markedCell,indicator,hz,h]
    simp [meanCell,expect,hh]

private theorem local_indicator (r : E → U) (c : E → V) (label : E → C)
    (e : E) (i : Option C) :
    depends (fun j => j ∈ nearby r c e) (fun z => indicator (markedCell r c label e z) i) := by
  intro x y he
  have hh : chosen r c x e ↔ chosen r c y e := by
    constructor <;> intro hh j hj
    · exact (he j hj).symm.trans (hh j hj)
    · exact (he j hj).trans (hh j hj)
  simp only [markedCell,hh]

def overlap (r : E → U) (c : E → V) (e : E) : Finset E :=
  Finset.univ.filter fun f => ∃ g ∈ nearby r c e, g ∈ nearby r c f

theorem overlap_le (r : E → U) (c : E → V) (B : ℕ)
    (degree : ∀ e, (nearby r c e).card ≤ B) (e : E) :
    (overlap r c e).card ≤ B^2 := by
  classical
  have hsub : overlap r c e ⊆ (nearby r c e).biUnion (nearby r c) := by
    intro f hf
    obtain ⟨g,hg,hgf⟩ := (Finset.mem_filter.mp hf).2
    refine Finset.mem_biUnion.2 ⟨g,hg,?_⟩
    exact (mem_nearby r c g f).2 (((mem_nearby r c f g).1 hgf).imp Eq.symm Eq.symm)
  refine (Finset.card_le_card hsub).trans ((Finset.card_biUnion_le).trans ?_)
  calc
    _ ≤ ∑ _ ∈ nearby r c e, B := Finset.sum_le_sum fun j _ => degree j
    _ = (nearby r c e).card * B := by simp
    _ ≤ B^2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ (degree e)

theorem degree_from_owners (r : E → U) (c : E → V) (R C' : ℕ)
    (rows : ∀ u, (Finset.univ.filter fun e => r e = u).card ≤ R)
    (cols : ∀ v, (Finset.univ.filter fun e => c e = v).card ≤ C') :
    ∀ e, (nearby r c e).card ≤ R+C' := by
  classical
  intro e
  have he : nearby r c e =
      (Finset.univ.filter fun f => r f = r e) ∪ (Finset.univ.filter fun f => c f = c e) := by
    ext f
    simp [nearby,eq_comm]
  rw [he]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add (rows _) (cols _))

/-- At most B² dependent marks per wire. A single legal deterministic
choice of the independent coins balances every cell simultaneously. -/
theorem choose_matching [Fintype C] (r : E → U) (c : E → V) (label : E → C) (B : ℕ)
    (degree : ∀ e, (nearby r c e).card ≤ B) :
    ∃ z : E → Bool,
      (Set.InjOn r {e | chosen r c z e}) ∧ (Set.InjOn c {e | chosen r c z e}) ∧
      ∀ i : C, ((∑ e : E, indicator (markedCell r c label e z) (some i)) -
      (∑ e : E, if label e = i then (1/2 : ℚ)^(nearby r c e).card else 0))^2 ≤
        (Fintype.card E : ℚ) * (B : ℚ)^2 := by
  classical
  let ref : E → Bool := fun _ => false
  let score := varianceScore Finset.univ (productWeight fair) (markedCell r c label)
  have hdep := expected_score_le_dependent (s := Finset.univ) (weight := productWeight fair)
    (label := markedCell r c label) (overlap r c) (productWeight_nonneg fair fair_nonneg)
    (productWeight_normalized fair fair_norm)
  have hind : ∀ e ∈ (Finset.univ : Finset E), ∀ f ∈ (Finset.univ : Finset E),
      f ∉ overlap r c e → ∀ i,
      expect (productWeight fair) (fun z =>
        indicator (markedCell r c label e z) i * indicator (markedCell r c label f z) i) =
        meanCell (productWeight fair) (markedCell r c label) e i *
        meanCell (productWeight fair) (markedCell r c label) f i := by
    intro e _ f _ hf i
    have hh : ∀ j, j ∈ nearby r c e → j ∈ nearby r c f → False :=
      fun j he hf' => hf (Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,he,hf'⟩)
    exact expectation_disjoint_supports fair fair_norm _ _ hh ref _ _
      (local_indicator r c label e i) (local_indicator r c label f i)
  obtain ⟨z,_,hz⟩ := J7SourceAssembly.exists_legal_labeling_by_conditioning ref fair fair_nonneg fair_norm score
  have hB : (∑ e : E, ((overlap r c e).card : ℚ)) ≤ (Fintype.card E : ℚ) * (B : ℚ)^2 := by
    calc
      _ ≤ ∑ _e : E, (B : ℚ)^2 := Finset.sum_le_sum fun e _ => by exact_mod_cast overlap_le r c B degree e
      _ = _ := by simp
  have hscore : score z ≤ (Fintype.card E : ℚ) * (B : ℚ)^2 := hz.trans ((hdep hind).trans hB)
  exact ⟨z,(chosen_matching r c z).1,(chosen_matching r c z).2,fun i => by
    have hc : (∑ e : E, centered (productWeight fair) (markedCell r c label) e (some i) z)^2 ≤ score z :=
      Finset.single_le_sum (f := fun i =>
        (∑ e : E, centered (productWeight fair) (markedCell r c label) e i z)^2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ (some i))
    simp only [centered, Finset.sum_sub_distrib, mean_survival] at hc
    exact hc.trans hscore⟩

#print axioms chosen_matching
#print axioms mean_survival
#print axioms overlap_le
#print axioms degree_from_owners
#print axioms choose_matching

end
end J7SeatMatching
