import P5MainIteratorSource

/-! Exact finite bad-cell estimate used in F.A3. Product counting under
uniform full cells is performed before transferring the estimate through
the nonuniform incidence cap. -/
namespace P5MainIterator
open scoped BigOperators Classical
open Real

noncomputable def markBase : ℝ := sqrt (sqrt 2)

theorem markBase_pow_four : markBase^4=2 := by
  rw [show markBase^4=(markBase^2)^2 by ring]
  unfold markBase
  rw [Real.sq_sqrt (sqrt_nonneg _),Real.sq_sqrt (by norm_num)]

theorem markBase_one_le : 1 ≤ markBase := by
  have h₀ : 0≤markBase := by unfold markBase; positivity
  by_contra! hn
  have h := pow_lt_pow_left₀ hn h₀ (by decide : (4:ℕ)≠0)
  rw [markBase_pow_four] at h
  norm_num at h

theorem badExponent_decay : markBase*(3/4:ℝ)<1 := by
  by_contra! h
  have h' : (4/3:ℝ)≤markBase := by linarith only [h]
  have hh := pow_le_pow_left₀ (by norm_num : 0≤(4/3:ℝ)) h' 4
  rw [markBase_pow_four] at hh
  norm_num at hh

variable {I B : Type*} [Fintype I] [Fintype B] [LinearOrder B]

noncomputable def badCells (I B : Type*) [Fintype I] [Fintype B] [LinearOrder B] : Finset (WordCell I B) :=
  Finset.univ.filter (fun u => 4*activeCount u<Fintype.card I)

noncomputable def markWeight (u : WordCell I B) : ℝ :=
  ((1:ℝ)/2)^activeCount u

omit [Fintype B] in
theorem markWeight_prod (u : WordCell I B) :
    markWeight u = ∏ i, if (u i).1≠(u i).2 then (1:ℝ)/2 else 1 := by
  rw [←Finset.prod_filter]
  unfold markWeight activeCount
  rw [Finset.prod_const,←Fintype.card_subtype]

omit [Fintype I] in
theorem letter_pair_sum :
    (∑ p : B × B, if p.1≠p.2 then (1:ℝ)/2 else 1) =
      (Fintype.card B:ℝ)*((Fintype.card B:ℝ)+1)/2 := by
  rw [Fintype.sum_prod_type]
  have h (a : B) : (∑ b : B, if a≠b then (1:ℝ)/2 else 1) =
      ((Fintype.card B:ℝ)+1)/2 := by
    calc
      _ = ∑ b : B, ((1:ℝ)/2 + if a=b then 1/2 else 0) := by
        apply Finset.sum_congr rfl
        intro b _
        by_cases h : a=b <;> norm_num [h]
      _ = _ := by simp [Finset.sum_add_distrib]; ring
  simp_rw [h]
  simp
  ring

theorem exact_inverse_moment :
    (∑ u : WordCell I B, markWeight u) =
      ((Fintype.card B:ℝ)*((Fintype.card B:ℝ)+1)/2)^Fintype.card I := by
  simp_rw [markWeight_prod]
  let f (_ : I) (p : B×B) : ℝ := if p.1≠p.2 then 1/2 else 1
  change (∑ u : (I→B×B),∏ i : I,f i (u i)) = _
  rw [←Fintype.prod_sum f]
  dsimp [f]
  simp_rw [letter_pair_sum]
  simp [←div_pow]

theorem bad_cells_count (hr : 2≤Fintype.card B) :
    ((badCells I B).card:ℝ) ≤ (Fintype.card (WordCell I B):ℝ) *
      (markBase*(3/4:ℝ))^Fintype.card I := by
  let q := Fintype.card I
  let r := Fintype.card B
  have hr' : 2≤(r:ℝ) := by exact_mod_cast hr
  have hh (u : WordCell I B) (hu : u∈badCells I B) : 1≤markBase^q*markWeight u := by
    have hc : 4*activeCount u≤q := ((Finset.mem_filter.mp hu).2).le
    have hpow := pow_le_pow_right₀ markBase_one_le hc
    rw [pow_mul,markBase_pow_four] at hpow
    calc
      _ = (2:ℝ)^activeCount u*markWeight u := by unfold markWeight; rw [←mul_pow]; norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_right hpow (by unfold markWeight; positivity)
  have hbase : (r:ℝ)*((r:ℝ)+1)/2 ≤ (r:ℝ)^2*(3/4:ℝ) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hr') (show 0≤(r:ℝ) by positivity)]
  calc
    _ = ∑ _u ∈ badCells I B,(1:ℝ) := by simp
    _ ≤ ∑ u ∈ badCells I B,markBase^q*markWeight u := Finset.sum_le_sum hh
    _ ≤ ∑ u : WordCell I B, markBase^q*markWeight u :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun u _ _ => by unfold markBase markWeight; positivity)
    _ = markBase^q * (∑ u : WordCell I B,markWeight u) := (Finset.mul_sum _ _ _).symm
    _ ≤ markBase^q * (((r:ℝ)^2*(3/4:ℝ))^q) := by
      rw [exact_inverse_moment]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase _) (by unfold markBase; positivity)
    _ = _ := by
      rw [card_wordCells (I:=I) (B:=B)]
      dsimp [q,r]
      push_cast
      rw [pow_mul,mul_pow,mul_pow]
      ring

#print axioms badExponent_decay
#print axioms markWeight_prod
#print axioms letter_pair_sum
#print axioms exact_inverse_moment
#print axioms bad_cells_count
end P5MainIterator
