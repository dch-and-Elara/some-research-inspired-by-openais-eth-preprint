import Lower

open Polynomial GrenetMcCoy Round4Transfer

namespace GrenetPaper

variable {R ι : Type*} [CommRing R] [Nontrivial R]

omit [Nontrivial R] in
private theorem not_determining_of_sparse_root_polynomial (x : ι → R) (t : ℕ)
    (p : R[X]) (hp : p ≠ 0) (hc : p.support.card ≤ 2 * t)
    (hz : ∀ i, p.eval (x i) = 0) : ¬ DeterminesUnboundedSparse x t := by
  intro h
  obtain ⟨f, g, hf, hg, hd⟩ :=
    (admissible_iff_split (d := p.natDegree) (t := t) p).mp ⟨le_rfl, hc⟩
  have he := h f g hf.2 hg.2 fun i => sub_eq_zero.mp (by rw [← eval_sub, ← hd, hz])
  exact hp (by rw [hd, he, sub_self])

/-- Fewer than 2t distinct supplied points cannot determine at-most-t-term inputs. -/
theorem not_determining_of_small_sample_set (x : ι → R) (t : ℕ) (s : Finset R)
    (hs : s.card < 2 * t) (hx : ∀ i, x i ∈ s) : ¬ DeterminesUnboundedSparse x t := by
  classical
  let p := ∏ r ∈ s, (X - C r)
  have hm : p.Monic := monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
  have hd : p.natDegree = s.card := by
    dsimp [p]
    rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
    simp
  apply not_determining_of_sparse_root_polynomial x t p hm.ne_zero
  · have hsub := supp_subset_range (show p.natDegree < s.card + 1 by omega)
    simpa using (Finset.card_le_card hsub).trans (by simpa using hs)
  · intro i
    simp only [p, eval_prod, eval_sub, eval_X, eval_C]
    exact Finset.prod_eq_zero (hx i) (sub_self _)

omit [Nontrivial R] in
private theorem support_odd_bound (p : R[X]) :
    (X * expand R 2 p).support ⊆ (Finset.range (p.natDegree + 1)).image
      (fun j : ℕ => 2 * j + 1) := by
  intro i hi
  apply mem_support_iff.mp at hi
  cases i with
  | zero => exact False.elim (hi (coeff_X_mul_zero _))
  | succ i =>
    rw [coeff_X_mul, coeff_expand (by decide : 0 < 2)] at hi
    split at hi
    next hd =>
      have hj := le_natDegree_of_ne_zero hi
      exact Finset.mem_image.mpr ⟨i / 2, Finset.mem_range.mpr (by omega), by omega⟩
    next => exact False.elim (hi rfl)

/-- A short set of nonzero squared values obstructs sampling, even when
the nodes of both signs and zero are present. -/
theorem not_determining_of_small_squared_sample_set (x : ι → R) (t : ℕ) (s : Finset R)
    (hs : s.card < 2 * t) (hx : ∀ i, x i = 0 ∨ (x i)^2 ∈ s) :
    ¬ DeterminesUnboundedSparse x t := by
  classical
  let p := ∏ r ∈ s, (X - C r)
  let q : R[X] := X * expand R 2 p
  have hm : p.Monic := monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _
  have hd : p.natDegree = s.card := by
    dsimp [p]
    rw [natDegree_prod_of_monic _ _ fun _ _ => monic_X_sub_C _]
    simp
  apply not_determining_of_sparse_root_polynomial x t q (monic_X.mul (hm.expand (by decide))).ne_zero
  · have hcard := (Finset.card_le_card (support_odd_bound p)).trans Finset.card_image_le
    simp only [Finset.card_range, hd] at hcard
    exact hcard.trans hs
  · intro i
    simp only [q, eval_mul, eval_X, expand_eval]
    rcases hx i with hzero | hmem
    · rw [hzero, zero_mul]
    · have h : p.eval ((x i)^2) = 0 := by
        simp only [p, eval_prod, eval_sub, eval_X, eval_C]
        exact Finset.prod_eq_zero hmem (sub_self _)
      rw [h, mul_zero]

/-- Dimension lower bound for every rational start, including negative steps. -/
theorem rational_prefix_lt_two_t (a b : ℚ) (m t : ℕ) (hm : m < 2 * t) :
    ¬ DeterminesUnboundedSparse (progression (fun i : Fin m => i.val) a b) t := by
  classical
  let x := progression (fun i : Fin m => i.val) a b
  exact not_determining_of_small_sample_set x t (Finset.univ.image x)
    (Finset.card_image_le.trans_lt (by simpa using hm))
    (fun i => Finset.mem_image_of_mem x (Finset.mem_univ i))


private theorem monomial_of_support_card_le_one (p : ℚ[X]) (h : p.support.card ≤ 1) :
    ∃ e c, p = monomial e c := by
  by_cases hz : p = 0
  · exact ⟨0, 0, by simp [hz]⟩
  have hc : p.support.card = 1 := by
    have hp := Finset.card_pos.mpr (nonempty_support_iff.mpr hz)
    omega
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hc
  refine ⟨e, p.coeff e, ?_⟩
  conv_lhs => rw [p.as_sum_support, he]
  simp

theorem one_term_determining_iff (x : ι → ℚ) :
    DeterminesUnboundedSparse x 1 ↔
      ∃ i j, x i ≠ 0 ∧ x j ≠ 0 ∧ |x i| ≠ |x j| := by
  constructor
  · intro h
    by_contra! hn
    by_cases hex : ∃ i, x i ≠ 0
    · obtain ⟨i, hi⟩ := hex
      apply not_determining_of_small_squared_sample_set x 1 {x i ^ 2} (by simp) _ h
      intro j
      by_cases hj : x j = 0
      · exact Or.inl hj
      right
      have hab := hn j i hj hi
      simp only [Finset.mem_singleton]
      calc
        (x j)^2 = |x j|^2 := (sq_abs (x j)).symm
        _ = |x i|^2 := congrArg (fun y : ℚ => y ^ 2) hab
        _ = (x i)^2 := sq_abs (x i)
    · push_neg at hex
      exact not_determining_of_small_squared_sample_set x 1 ∅ (by simp)
        (fun i => Or.inl (hex i)) h
  · rintro ⟨i, j, hi, hj, hij⟩ f g hf hg h
    obtain ⟨e, c, rfl⟩ := monomial_of_support_card_le_one f hf
    obtain ⟨d, a, rfl⟩ := monomial_of_support_card_le_one g hg
    have he : c * (x i)^e = a * (x i)^d := by simpa only [eval_monomial] using h i
    have hd : c * (x j)^e = a * (x j)^d := by simpa only [eval_monomial] using h j
    by_cases hc : c = 0
    · have ha : a = 0 := by
        rw [hc, zero_mul, eq_comm, mul_eq_zero] at he
        exact he.resolve_right (pow_ne_zero _ hi)
      simp [hc, ha]
    · have hcross : (x i)^e * (x j)^d = (x i)^d * (x j)^e := by
        apply mul_left_cancel₀ hc
        calc
          _ = (c * (x i)^e) * (x j)^d := by ring
          _ = (a * (x i)^d) * (x j)^d := by rw [he]
          _ = (a * (x j)^d) * (x i)^d := by ring
          _ = (c * (x j)^e) * (x i)^d := by rw [← hd]
          _ = _ := by ring
      have hu : (x i / x j)^e = (x i / x j)^d := by
        simp only [div_pow]
        exact (div_eq_div_iff (pow_ne_zero _ hj) (pow_ne_zero _ hj)).mpr hcross
      have hu₀ : 0 < |x i / x j| := abs_pos.mpr (div_ne_zero hi hj)
      have hu₁ : |x i / x j| ≠ 1 := by
        intro he
        have hm : |(x i / x j) * x j| = |x j| := by rw [abs_mul, he, one_mul]
        rw [div_mul_cancel₀ (x i) hj] at hm
        exact hij hm
      have hed := pow_right_injective₀ hu₀ hu₁ (by simpa only [abs_pow] using congrArg abs hu)
      subst d
      have hca := mul_right_cancel₀ (pow_ne_zero _ hi) he
      rw [hca]

private theorem abs_ne_of_sq_ne {x y : ℚ} (h : x^2 ≠ y^2) : |x| ≠ |y| := by
  intro he
  have h' := congrArg (fun z : ℚ => z ^ 2) he
  change |x| ^ 2 = |y| ^ 2 at h'
  rw [sq_abs, sq_abs] at h'
  exact h h'

/-- The exact shortest prefix at sparsity one, for every rational start. -/
def oneTermLength (z : ℚ) : ℕ :=
  if z = -1 then 4 else if z = 0 ∨ z = -1 / 2 then 3 else 2

theorem rational_one_term_prefix_exact (z : ℚ) (m : ℕ) :
    DeterminesUnboundedSparse (fun i : Fin m => z + i.val) 1 ↔ oneTermLength z ≤ m := by
  classical
  by_cases hz1 : z = -1
  · subst z
    rw [show oneTermLength (-1) = 4 by norm_num [oneTermLength]]
    constructor
    · intro h
      by_contra! hs
      apply not_determining_of_small_squared_sample_set _ 1 ({1} : Finset ℚ) (by simp) _ h
      intro i
      have hi : i.val < 3 := i.isLt.trans_le (by omega)
      interval_cases hval : i.val <;> norm_num [hval]
    · intro hm
      apply (one_term_determining_iff _).mpr
      refine ⟨⟨0, by omega⟩, ⟨3, by omega⟩, ?_, ?_, abs_ne_of_sq_ne ?_⟩ <;> norm_num
  · by_cases hz0 : z = 0
    · subst z
      rw [show oneTermLength 0 = 3 by norm_num [oneTermLength]]
      constructor
      · intro h
        by_contra! hs
        apply not_determining_of_small_squared_sample_set _ 1 ({1} : Finset ℚ) (by simp) _ h
        intro i
        have hi : i.val < 2 := i.isLt.trans_le (by omega)
        interval_cases hval : i.val <;> norm_num [hval]
      · intro hm
        apply (one_term_determining_iff _).mpr
        refine ⟨⟨1, by omega⟩, ⟨2, by omega⟩, ?_, ?_, abs_ne_of_sq_ne ?_⟩ <;> norm_num
    · by_cases hzh : z = -1 / 2
      · subst z
        rw [show oneTermLength (-1/2) = 3 by norm_num [oneTermLength]]
        constructor
        · intro h
          by_contra! hs
          apply not_determining_of_small_squared_sample_set _ 1 ({1/4} : Finset ℚ) (by simp) _ h
          intro i
          have hi : i.val < 2 := i.isLt.trans_le (by omega)
          interval_cases hval : i.val <;> norm_num [hval]
        · intro hm
          apply (one_term_determining_iff _).mpr
          refine ⟨⟨0, by omega⟩, ⟨2, by omega⟩, ?_, ?_, abs_ne_of_sq_ne ?_⟩ <;> norm_num
      · simp only [oneTermLength, if_neg hz1, if_neg (not_or.mpr ⟨hz0, hzh⟩)]
        constructor
        · intro h
          by_contra! hm
          apply rational_prefix_lt_two_t z 1 m 1 (by simpa using hm)
          intro f g hf hg he
          apply h f g hf hg
          simpa [progression] using he
        · intro hm
          apply (one_term_determining_iff _).mpr
          refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_, ?_, abs_ne_of_sq_ne ?_⟩
          · simpa using hz0
          · simp only [Nat.cast_one]
            intro h
            apply hz1
            linarith
          · simp only [Nat.cast_zero, add_zero, Nat.cast_one]
            intro h
            apply hzh
            nlinarith

theorem rational_one_term_progression_exact (a b : ℚ) (hb : b ≠ 0) (m : ℕ) :
    DeterminesUnboundedSparse (progression (fun i : Fin m => i.val) a b) 1 ↔
      oneTermLength (a / b) ≤ m := by
  rw [← rational_one_term_prefix_exact]
  rw [one_term_determining_iff, one_term_determining_iff]
  have hp (i : Fin m) : progression (fun j : Fin m => j.val) a b i = (a/b+i.val)*b := by
    simp [progression, add_mul, div_mul_cancel₀ _ hb]
  have hcancel (u v : ℚ) : u * |b| = v * |b| ↔ u = v :=
    ⟨mul_right_cancel₀ (abs_ne_zero.mpr hb), fun h => congrArg (fun x => x * |b|) h⟩
  simp [hp, abs_mul, hb, hcancel]

end GrenetPaper
