import Paper1LiteralPeriod
import BooleanCube.SymmetricAnalysis

/-! Exact finite cost of the literal single residue class in (11).
The right tail is a reflection of the actual left tail, not independently
chosen. The bound is the geometric sum in the published argument. -/

namespace LocalReconstruction.Paper1Coverage

open Finset
open scoped BigOperators
noncomputable section

def literalRatio (q l : ℕ) : ℝ := (l:ℝ) / ((q:ℝ)-l+1)

theorem literal_ratio_nonneg {q l : ℕ} (hl : l ≤ q) :
    0 ≤ literalRatio q l := by
  unfold literalRatio
  exact div_nonneg (Nat.cast_nonneg l) (by linarith [show (l:ℝ) ≤ q by exact_mod_cast hl])

theorem literal_ratio_lt_one {q l : ℕ} (hl : 2*l < q) :
    literalRatio q l < 1 := by
  unfold literalRatio
  have h : 2*(l:ℝ) < q := by exact_mod_cast hl
  exact (div_lt_one (by linarith [Nat.cast_nonneg (α := ℝ) l])).mpr (by linarith)

private theorem binomial_ray_step {q l k : ℕ} (hl : l ≤ q) (hk : k < l) :
    (q.choose k:ℝ) ≤ literalRatio q l * (q.choose (k+1):ℝ) := by
  have hkl : (k:ℝ)+1 ≤ l := by exact_mod_cast Nat.succ_le_of_lt hk
  have hlq : (l:ℝ) ≤ q := by exact_mod_cast hl
  have hqk : 0 < (q:ℝ)-k := by linarith
  have hqL : 0 < (q:ℝ)-l+1 := by linarith
  have hcast := congrArg (fun n : ℕ => (n:ℝ)) (Nat.choose_succ_right_eq q k)
  push_cast [Nat.cast_sub (show k ≤ q by omega)] at hcast
  have eq : (q.choose k:ℝ) = ((k:ℝ)+1)/((q:ℝ)-k) * (q.choose (k+1):ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hqk.ne').mpr
    nlinarith only [hcast]
  rw [eq, literalRatio]
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  exact (div_le_div_of_nonneg_right hkl hqk.le).trans
    (div_le_div_of_nonneg_left (Nat.cast_nonneg _) hqL (by linarith))

theorem binomial_ray_geometric (q l s : ℕ) (hl : l ≤ q) (hs : s ≤ l) :
    (q.choose (l-s):ℝ) ≤ (q.choose l:ℝ) * (literalRatio q l)^s := by
  induction s with
  | zero => simp
  | succ s ih =>
    have h := ih (by omega)
    have step := binomial_ray_step (q := q) (l := l) (k := l-(s+1)) hl (by omega)
    rw [show l-(s+1)+1 = l-s by omega] at step
    calc
      _ ≤ literalRatio q l * (q.choose (l-s):ℝ) := step
      _ ≤ literalRatio q l * ((q.choose l:ℝ) * (literalRatio q l)^s) :=
        mul_le_mul_of_nonneg_left h (literal_ratio_nonneg hl)
      _ = _ := by rw [pow_succ]; ring

private theorem geom_tail_bound (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t < 1) (n : ℕ) :
    (∑ j ∈ range n, t^(j+1)) ≤ t/(1-t) := by
  have sum_formula (m : ℕ) : (1-t) * (∑ j ∈ range m, t^(j+1)) = t - t^(m+1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, mul_add, ih, pow_succ t (m+1)]
      ring
  apply (le_div_iff₀ (sub_pos.mpr ht₁)).mpr
  rw [mul_comm, sum_formula]
  exact sub_le_self _ (pow_nonneg ht₀ _)

def literalPeriodicLeft (q l : ℕ) : Finset ℕ :=
  (literalPeriodicLayers q l).filter (· < l)

private theorem index_distance {q l k : ℕ} (hk : k ∈ literalPeriodicLeft q l) :
    let j := (l-k)/literalPeriod q l - 1
    j < l ∧ literalPeriod q l*(j+1) = l-k := by
  have h₁ := (mem_filter.mp hk).2
  have hmod := (mem_literalPeriodicLayers.mp (mem_filter.mp hk).1).2
  have hd := (Nat.modEq_iff_dvd' h₁.le).mp hmod.symm
  have hx := Nat.div_mul_cancel hd
  have hpos : 0 < (l-k)/literalPeriod q l := by
    by_contra! hz
    rw [Nat.eq_zero_of_le_zero hz, zero_mul] at hx
    omega
  have hle := Nat.div_le_self (l-k) (literalPeriod q l)
  dsimp only
  refine ⟨by omega,?_⟩
  rw [show (l-k)/literalPeriod q l-1+1 = (l-k)/literalPeriod q l by omega, mul_comm, hx]

theorem literal_left_tail_cost {q l : ℕ} (hl : 2*l < q) :
    (∑ k ∈ literalPeriodicLeft q l, (q.choose k:ℝ)) ≤
      (q.choose l:ℝ) * ((literalRatio q l)^(literalPeriod q l) /
        (1-(literalRatio q l)^(literalPeriod q l))) := by
  classical
  let idx := fun k : ℕ => (l-k)/literalPeriod q l-1
  let left := literalPeriodicLeft q l
  let t := (literalRatio q l)^(literalPeriod q l)
  have hlq : l ≤ q := by omega
  have t0 : 0 ≤ t := pow_nonneg (literal_ratio_nonneg hlq) _
  have t1 : t < 1 := pow_lt_one₀ (literal_ratio_nonneg hlq) (literal_ratio_lt_one hl)
    (Nat.ne_of_gt (literal_period_positive hl))
  have hinj : Set.InjOn idx ↑left := by
    intro x hx y hy eq
    have dx := (index_distance hx).2
    have dy := (index_distance hy).2
    change literalPeriod q l * (idx x+1) = l-x at dx
    change literalPeriod q l * (idx y+1) = l-y at dy
    rw [eq] at dx
    have hx' : x ∈ (literalPeriodicLayers q l).filter (· < l) := hx
    have hy' : y ∈ (literalPeriodicLayers q l).filter (· < l) := hy
    have ha := (mem_filter.mp hx').2
    have hb := (mem_filter.mp hy').2
    omega
  have hrange : left.image idx ⊆ range l := by
    intro z hz
    obtain ⟨k,hk,rfl⟩ := mem_image.mp hz
    exact mem_range.mpr (index_distance hk).1
  calc
    _ ≤ ∑ k ∈ left, (q.choose l:ℝ)*t^(idx k+1) := by
      apply sum_le_sum
      intro k hk
      have lt := (mem_filter.mp hk).2
      have hb := binomial_ray_geometric q l (l-k) hlq (by omega)
      rw [show l-(l-k) = k by omega, ← (index_distance hk).2, pow_mul] at hb
      exact hb
    _ = ∑ j ∈ left.image idx, (q.choose l:ℝ)*t^(j+1) := by rw [sum_image hinj]
    _ ≤ ∑ j ∈ range l, (q.choose l:ℝ)*t^(j+1) :=
      sum_le_sum_of_subset_of_nonneg hrange fun _ _ _ =>
        mul_nonneg (Nat.cast_nonneg _) (pow_nonneg t0 _)
    _ = (q.choose l:ℝ) * ∑ j ∈ range l, t^(j+1) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (geom_tail_bound t t0 t1 l) (Nat.cast_nonneg _)

private theorem literal_class_partition {q l : ℕ} (hl : 2*l < q) :
    literalPeriodicLayers q l =
      insert l (insert (q-l) (literalPeriodicLeft q l ∪ (literalPeriodicLeft q l).image (q-·))) := by
  ext k
  constructor
  · intro hk
    have bk := (mem_literalPeriodicLayers.mp hk).1
    by_cases h₁ : k = l
    · simp [h₁]
    by_cases h₂ : k = q-l
    · simp [h₂]
    have hleft : k < l ∨ q-l < k := by
      by_contra! nh
      exact no_literal_periodic_between_centers hl (by omega) (by omega) hk
    rcases hleft with hleft | hright
    · exact mem_insert_of_mem (mem_insert_of_mem (mem_union_left _ (mem_filter.mpr ⟨hk,hleft⟩)))
    · have hc : q-k ∈ literalPeriodicLeft q l :=
        mem_filter.mpr ⟨literal_periodic_reflect hl hk,by omega⟩
      apply mem_insert_of_mem (mem_insert_of_mem (mem_union_right _ _))
      exact mem_image.mpr ⟨q-k,hc,by omega⟩
  · simp only [mem_insert, mem_union, mem_image]
    rintro (rfl | rfl | hk | ⟨j,hj,rfl⟩)
    · exact (literal_periodic_centers hl).1
    · exact (literal_periodic_centers hl).2
    · exact (mem_filter.mp hk).1
    · exact literal_periodic_reflect hl (mem_filter.mp hj).1

/-- The exact finite reflection identity, with the central pair paid exactly once. -/
theorem literal_periodic_cost_split {q l : ℕ} (hl : 2*l < q) :
    (∑ k ∈ literalPeriodicLayers q l, (q.choose k:ℝ)) =
      2*(q.choose l:ℝ) + 2*(∑ k ∈ literalPeriodicLeft q l,(q.choose k:ℝ)) := by
  classical
  let L := literalPeriodicLeft q l
  let R := L.image (q-·)
  have below : ∀ k ∈ L, k < l := fun _ hk => (mem_filter.mp hk).2
  have above : ∀ k ∈ R, q-l < k := by
    intro k hk
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hk
    have := below j hj
    omega
  have hd : Disjoint L R := disjoint_left.mpr fun k hL hR => by
    have := below k hL
    have := above k hR
    omega
  have hR : (∑ k ∈ R, (q.choose k:ℝ)) = ∑ k ∈ L, (q.choose k:ℝ) := by
    unfold R
    rw [sum_image]
    · exact sum_congr rfl fun k hk => by rw [Nat.choose_symm (by have := below k hk; omega)]
    · intro a ha b hb eq
      have h₁ := below a ha
      have h₂ := below b hb
      change q-a = q-b at eq
      omega
  have noUpper : q-l ∉ L ∪ R := by
    simp only [mem_union, not_or]
    exact ⟨fun hp => by have := below _ hp; omega, fun hp => by have := above _ hp; omega⟩
  have noLower : l ∉ insert (q-l) (L ∪ R) := by
    simp only [mem_insert, mem_union, not_or]
    exact ⟨by omega,fun hp => by have := below _ hp; omega,fun hp => by have := above _ hp; omega⟩
  rw [literal_class_partition hl]
  change (∑ k ∈ insert l (insert (q-l) (L ∪ R)), (q.choose k:ℝ)) = _
  rw [sum_insert noLower, sum_insert noUpper, sum_union hd, hR, Nat.choose_symm (by omega : l ≤ q)]
  ring

/-- The geometric outer cost in §4.2 for the actual (11) layer set. -/
theorem literal_periodic_total_cost {q l : ℕ} (hl : 2*l < q) :
    (∑ k ∈ literalPeriodicLayers q l, (q.choose k:ℝ)) ≤ 2*(q.choose l:ℝ) *
      (1+(literalRatio q l)^(literalPeriod q l)/(1-(literalRatio q l)^(literalPeriod q l))) := by
  rw [literal_periodic_cost_split hl]
  linarith only [literal_left_tail_cost hl]

end
end LocalReconstruction.Paper1Coverage

#print axioms LocalReconstruction.Paper1Coverage.literal_ratio_nonneg
#print axioms LocalReconstruction.Paper1Coverage.literal_ratio_lt_one
#print axioms LocalReconstruction.Paper1Coverage.binomial_ray_geometric
#print axioms LocalReconstruction.Paper1Coverage.literal_left_tail_cost
#print axioms LocalReconstruction.Paper1Coverage.literal_periodic_cost_split
#print axioms LocalReconstruction.Paper1Coverage.literal_periodic_total_cost
