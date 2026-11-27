import GrenetPaper
import HalfBridge

open Polynomial Matrix GrenetMcCoy
open scoped BigOperators

namespace GrenetPaper

private theorem scaleRoots_X_pow_two_sub (R : Type*) [CommRing R] [Nontrivial R]
    (c b : R) :
    ((X^2 - C c : R[X]).scaleRoots b) = X^2 - C (c*b^2) := by
  ext i
  rw [coeff_scaleRoots, natDegree_X_pow_sub_C,
    coeff_sub, coeff_sub, coeff_X_pow, coeff_C, coeff_C]
  by_cases hi : i = 0
  · subst i
    simp
  · by_cases hi2 : i = 2
    · subst i
      simp
    · simp [hi, hi2]

private theorem scaleRoots_monic_mul {R : Type*} [CommRing R] [Nontrivial R]
    (p q : R[X]) (hp : p.Monic) (hq : q.Monic) (b : R) :
    (p * q).scaleRoots b = p.scaleRoots b * q.scaleRoots b := by
  apply mul_scaleRoots'
  rw [hp.leadingCoeff, hq.leadingCoeff, one_mul]
  exact one_ne_zero

private theorem scaleRoots_monic_prod {R α : Type*} [CommRing R] [Nontrivial R]
    (s : Finset α) (p : α → R[X]) (hp : ∀ x ∈ s, (p x).Monic) (b : R) :
    (∏ x ∈ s, p x).scaleRoots b = ∏ x ∈ s, (p x).scaleRoots b := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [one_scaleRoots]
  | insert a s ha ih =>
    have hpa := hp a (Finset.mem_insert_self a s)
    have hps : ∀ x ∈ s, (p x).Monic := fun x hx => hp x (Finset.mem_insert_of_mem hx)
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      scaleRoots_monic_mul _ _ hpa (monic_prod_of_monic _ _ hps), ih hps]

/-- The fixed-step witness is literally the product in the paper,
also over a non-domain and for a nonunit regular step. -/
theorem scaledWitness_eq_product {R : Type*} [CommRing R] [Nontrivial R]
    (n : ℕ) (b : R) :
    scaledWitness n b = X * ∏ j ∈ Finset.range n, (X^2 - C ((((j : R)+1)*b)^2)) := by
  let g (j : ℕ) : R[X] := X^2 - C (((j : R)+1)^2)
  have hm : ∀ j : ℕ, (g j).Monic := fun j => monic_X_pow_sub_C _ (by decide)
  have hmap :
      (Round4Prefix.symmetricWitness n).map (Int.castRingHom R) = X * ∏ j ∈ Finset.range n, g j := by
    rw [Round4Prefix.symmetricWitness_eq_product]
    simp [g, Polynomial.map_prod]
  have hX : (X : R[X]).scaleRoots b = X := by
    ext i
    by_cases hi : i = 1
    · subst i
      simp
    · simp [coeff_X, Ne.symm hi]
  rw [scaledWitness, hmap, scaleRoots_monic_mul _ _ monic_X
    (monic_prod_of_monic _ _ (fun j _ => hm j)), hX,
    scaleRoots_monic_prod _ _ (fun j _ => hm j)]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  simp only [g, scaleRoots_X_pow_two_sub, mul_pow]

end GrenetPaper

namespace GrenetRational

/-- The finite numerical examples in the text use exactly the same
threshold expression as the general theorem. -/
theorem published_threshold_examples :
    threshold 0 1 = 3 ∧ threshold (-1/2) 1 = 3 ∧ threshold (-1) 1 = 4 ∧
    threshold (-7/3) 2 = 4 ∧ threshold (-5/4) 2 = 4 ∧
    threshold (-5/2) 2 = 7 ∧ threshold (-3) 2 = 8 := by
  decide +kernel


/-- The cardinality conventions on full minors in Appendix A. -/
theorem fullMinorIdeal_empty_columns {R ρ κ : Type*} [CommRing R]
    [Fintype κ] [DecidableEq κ] [IsEmpty κ] (A : Matrix ρ κ R) :
    fullMinorIdeal A = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  apply Ideal.subset_span
  exact ⟨fun i => isEmptyElim i, by simp⟩

theorem fullMinorIdeal_fewer_rows {R ρ κ : Type*} [CommRing R] [Fintype ρ]
    [Fintype κ] [DecidableEq κ] (A : Matrix ρ κ R)
    (h : Fintype.card ρ < Fintype.card κ) : fullMinorIdeal A = ⊥ := by
  have hzero : KillsFullMinors A 1 := by
    apply (killsFullMinors_iff_injective_rows A 1).mpr
    intro rows hr
    exact False.elim ((not_le_of_gt h) (Fintype.card_le_of_injective rows hr))
  rw [fullMinorIdeal, Ideal.span_eq_bot]
  rintro x ⟨rows, rfl⟩
  simpa using hzero rows

/-- Every positive rational normalized start attains the 2t lower bound. -/
theorem threshold_of_positive (z : ℚ) (hz : 0 < z) (t : ℕ) (ht : 1 ≤ t) :
    threshold z t = 2*t := by
  have hp : firstPositive z = 0 := by
    have h : 0 < normalizedNode z 0 := by simpa [normalizedNode] using hz
    exact Nat.eq_zero_of_le_zero ((node_pos_iff z 0).mp h)
  have hn : negativeLength z = 0 := by
    by_contra h
    have hz' := (node_neg_iff z 0).mpr (Nat.pos_of_ne_zero h)
    simp [normalizedNode, not_lt_of_ge hz.le] at hz'
  have ht' : ¬2*t ≤ 0 := by omega
  by_cases h : 2 < z.den <;> simp [threshold, signThreshold, h, hn, hp, ht']

/-- The centered integer grid is the unique worst rational start. -/
theorem threshold_eq_four_t_iff (z : ℚ) (t : ℕ) (ht : 1 ≤ t) :
    threshold z t = 4*t ↔ z = -((2*t-1 : ℕ) : ℚ) := by
  let k := 2*t
  have hk : 1 ≤ k := by dsimp [k]; omega
  have h4 : 4*t = k+k := by dsimp [k]; omega
  rw [h4]
  change threshold z t = k+k ↔ z = -((k-1 : ℕ) : ℚ)
  constructor
  · intro h
    by_cases hd : 2 < z.den
    · rw [threshold, if_pos hd] at h
      change k = k+k at h
      omega
    · rw [threshold, if_neg hd] at h
      change signThreshold z k = k+k at h
      have hq : negativeLength z < k := by
        by_contra! hq
        simp only [signThreshold, if_pos hq] at h
        omega
      have hp : firstPositive z = k := by
        rw [signThreshold, if_neg (not_le_of_gt hq)] at h
        omega
      have hlow : ¬normalizedNode z (k-1) < 0 := by
        rw [node_neg_iff]
        omega
      have hhigh : ¬0 < normalizedNode z (k-1) := by
        rw [node_pos_iff, hp]
        omega
      have hz : normalizedNode z (k-1) = 0 := by linarith
      unfold normalizedNode at hz
      linarith
  · intro h
    have hd : z.den ≤ 2 := (den_le_two_iff_double_integer z).mpr
      ⟨-2*((k-1 : ℕ) : ℤ), by rw [h]; push_cast; ring⟩
    rw [threshold, if_neg (not_lt_of_ge hd)]
    change signThreshold z k = k+k
    have hz0 : normalizedNode z (k-1) = 0 := by simp [normalizedNode, h]
    have hq : negativeLength z < k := by
      have hh : ¬ normalizedNode z (k-1) < 0 := by rw [hz0]; exact lt_irrefl _
      rw [node_neg_iff] at hh
      omega
    have hpos1 : ¬ firstPositive z ≤ k-1 := by
      rw [← node_pos_iff, hz0]
      exact lt_irrefl _
    have hpos2 : firstPositive z ≤ k := by
      apply (node_pos_iff z k).mp
      simp [normalizedNode, h, Nat.cast_sub hk]
    rw [signThreshold, if_neg (not_le_of_gt hq)]
    omega

/-- The introductory positive-characteristic example holds even on the
entire coefficient ring. -/
theorem characteristic_two_collision :
    ∃ f g : (ZMod 2)[X], f.support.card = 1 ∧ g.support.card = 1 ∧ f ≠ g ∧
      ∀ x, f.eval x = g.eval x := by
  refine ⟨X^2, X, ?_, ?_, ?_, ?_⟩
  · rw [X_pow_eq_monomial, support_monomial _ one_ne_zero, Finset.card_singleton]
  · rw [Polynomial.X, support_monomial _ one_ne_zero, Finset.card_singleton]
  · intro he
    have h := congrArg (fun p : (ZMod 2)[X] => p.coeff 2) he
    simp [coeff_X_pow, coeff_X] at h
  · intro x
    simp only [eval_pow, eval_X]
    fin_cases x <;> decide +kernel

theorem zero_step_collision {R : Type*} [CommRing R] [Nontrivial R]
    (a : R) (m : ℕ) : ¬ Round4Transfer.DeterminesUnboundedSparse (ringPrefix a 0 m) 1 := by
  classical
  apply GrenetPaper.not_determining_of_small_sample_set _ 1 {a} (by simp)
  intro i
  simp [ringPrefix, Round4Transfer.progression]
end GrenetRational
