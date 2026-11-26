import SourceDensity
import ProductVariance
import FiniteSelection
import Mathlib.Tactic.Positivity

namespace S8

open scoped BigOperators
open SourceDensity

variable {P C Ω : Type*} [Fintype P] [Fintype C] [DecidableEq C] [Nonempty C]

def collision (cell : P → C) : ℚ :=
  ∑ c, ((fiberCount cell c : ℚ) - (Fintype.card P : ℚ) / Fintype.card C)^2

omit [Nonempty C] in
theorem collision_nonneg (cell : P → C) : 0 ≤ collision cell :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [Nonempty C] in
theorem sum_fiberCounts (cell : P → C) :
    (∑ c, (fiberCount cell c : ℚ)) = Fintype.card P := by
  simp only [fiberCount, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  simpa using Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset P)) (t := (Finset.univ : Finset C)) (g := cell)
    (fun _ _ => Finset.mem_univ _) (fun _ => (1 : ℚ))

omit [Nonempty C] [Fintype C] in
private theorem count_eq_sum (cell : P → C) (c : C) :
    (fiberCount cell c : ℚ) = ∑ p, if cell p = c then 1 else 0 := by
  simp only [fiberCount, Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter, apply_ite (Nat.cast : ℕ → ℚ), Nat.cast_one, Nat.cast_zero]

theorem collision_pair (cell : P → C) :
    collision cell =
      (∑ e, ∑ f, if cell e = cell f then (1 : ℚ) else 0) -
      (Fintype.card P : ℚ)^2 / Fintype.card C := by
  have hc : (Fintype.card C : ℚ) ≠ 0 := by positivity
  have pairs : (∑ c, (fiberCount cell c : ℚ)^2) =
      ∑ e, ∑ f, if cell e = cell f then (1 : ℚ) else 0 := by
    simp only [count_eq_sum, pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm (s := (Finset.univ : Finset C))]
    apply Finset.sum_congr rfl
    intro e _
    rw [Finset.sum_comm (s := (Finset.univ : Finset C))]
    apply Finset.sum_congr rfl
    intro f _
    rw [Finset.sum_eq_single (cell e)]
    · by_cases he : cell e = cell f
      · simp [he]
      · simp [he, Ne.symm he]
    · intro c _ h
      simp [Ne.symm h]
    · simp
  unfold collision
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib, pairs,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, sum_fiberCounts]
  field_simp
  ring

/-- Counting potentially dependent ordered pairs suffices. No hypothesis about
    pairs in the charged set is needed. -/
theorem mean_collision_le [Fintype Ω] (μ : Ω → ℚ) (mass : ∑ ω, μ ω = 1)
    (nonneg : ∀ ω, 0 ≤ μ ω) (cell : Ω → P → C) (bad : Finset (P × P))
    (independentAgreement : ∀ e f, (e,f) ∉ bad →
      (∑ ω, μ ω * (if cell ω e = cell ω f then 1 else 0)) = 1 / Fintype.card C) :
    (∑ ω, μ ω * collision (cell ω)) ≤ bad.card := by
  classical
  have swap : (∑ ω, μ ω * collision (cell ω)) =
      (∑ e, ∑ f, ((∑ ω, μ ω * (if cell ω e = cell ω f then 1 else 0)) -
        1 / Fintype.card C)) := by
    simp only [collision_pair, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
      mass, one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    · simp only [Finset.mul_sum]
      rw [Finset.sum_comm (s := (Finset.univ : Finset Ω))]
      exact Finset.sum_congr rfl (fun e _ => Finset.sum_comm)
    · ring
  rw [swap]
  have rhs : (bad.card : ℚ) =
      ∑ e, ∑ f, if (e,f) ∈ bad then (1 : ℚ) else 0 := by
    rw [← Fintype.sum_prod_type (f := fun p : P × P => if p ∈ bad then (1 : ℚ) else 0)]
    simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
      Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [rhs]
  apply Finset.sum_le_sum
  intro e _
  apply Finset.sum_le_sum
  intro f _
  by_cases h : (e,f) ∈ bad
  · simp only [if_pos h]
    have prob : (∑ ω, μ ω * (if cell ω e = cell ω f then 1 else 0)) ≤ 1 := by
      calc
        _ ≤ ∑ ω, μ ω := by
          apply Finset.sum_le_sum
          intro ω _
          split_ifs <;> simp [nonneg ω]
        _ = 1 := mass
    exact (sub_le_self _ (by positivity)).trans prob
  · rw [if_neg h, independentAgreement e f h, sub_self]

/-- Finite averaging with a nonnegative probability law. -/
theorem exists_of_mean_le [Fintype Ω] (μ Z : Ω → ℚ)
    (mass : ∑ ω, μ ω = 1) (nonneg : ∀ ω, 0 ≤ μ ω)
    (B : ℚ) (average : (∑ ω, μ ω * Z ω) ≤ B) : ∃ ω, Z ω ≤ B := by
  classical
  by_contra! hall
  obtain ⟨ω, hω, _⟩ := FiniteSelection.exists_avoid_bad (J := Empty) μ (fun _ _ => False)
    (fun _ => 0) nonneg mass (by simp) (by simp)
  have hs : (∑ x, μ x * B) < ∑ x, μ x * Z x := by
    apply Finset.sum_lt_sum
    · exact fun x _ => mul_le_mul_of_nonneg_left (hall x).le (nonneg x)
    · exact ⟨ω, Finset.mem_univ _, mul_lt_mul_of_pos_left (hall ω) hω⟩
  rw [← Finset.sum_mul, mass, one_mul] at hs
  exact (not_lt_of_ge average) hs

theorem cell_load_of_potential (cell : P → C) (T : ℚ) (hT : collision cell ≤ T)
    (hF : T * (Fintype.card C : ℚ)^2 ≤ (Fintype.card P : ℚ)^2) (i : C) :
    (fiberCount cell i : ℚ) ≤ 2 * Fintype.card P / Fintype.card C := by
  have hD : (0 : ℚ) < Fintype.card C := by positivity
  have hi : ((fiberCount cell i : ℚ) - (Fintype.card P : ℚ) / Fintype.card C)^2 ≤
      collision cell :=
    Finset.single_le_sum (f := fun j => ((fiberCount cell j : ℚ) -
      (Fintype.card P : ℚ) / Fintype.card C)^2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hh := (hi.trans hT).trans
    (show T ≤ ((Fintype.card P : ℚ) / Fintype.card C)^2 by
      rw [div_pow]; exact (le_div_iff₀ (sq_pos_of_pos hD)).2 hF)
  have ha : |(fiberCount cell i : ℚ) - (Fintype.card P : ℚ) / Fintype.card C| ≤
      (Fintype.card P : ℚ) / Fintype.card C := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    simpa [sq_abs] using hh
  rw [mul_div_assoc, two_mul]
  exact sub_le_iff_le_add.mp ((le_abs_self _).trans ha)

/-- MAIN uses the sum over all assignment-variable coordinate potentials. -/
theorem main_certificates_of_moments {L R I : Type*} [Fintype L] [DecidableEq L]
    [Nonempty L] [Fintype R] [Fintype I] [Fintype Ω]
    (μ : Ω → ℚ) (mass : ∑ ω, μ ω = 1) (nonneg : ∀ ω, 0 ≤ μ ω)
    (cell : Ω → P → C) (assignment : Ω → I → R → L)
    (M X : ℚ) (hpM : 0 < M) (hpX : 0 < X)
    (incidenceMoment : (∑ ω, μ ω * collision (cell ω)) ≤ M)
    (groupMoment : (∑ ω, μ ω * ∑ i, collision (assignment ω i)) ≤ X)
    (incidenceFeasible : 2 * M * (Fintype.card C : ℚ)^2 ≤ (Fintype.card P : ℚ)^2)
    (groupFeasible : 2 * X * (Fintype.card L : ℚ)^2 ≤ (Fintype.card R : ℚ)^2) :
    ∃ ω, (∀ c, (fiberCount (cell ω) c : ℚ) ≤ 2 * Fintype.card P / Fintype.card C) ∧
      ∀ i g, (fiberCount (assignment ω i) g : ℚ) ≤ 2 * Fintype.card R / Fintype.card L := by
  let Xi ω := ∑ i, collision (assignment ω i)
  have hXi (ω : Ω) : 0 ≤ Xi ω := Finset.sum_nonneg fun i _ => collision_nonneg _
  let Z ω := collision (cell ω) / M + Xi ω / X
  have avg : (∑ ω, μ ω * Z ω) ≤ 2 := by
    calc
      _ = (∑ ω, μ ω * collision (cell ω)) / M + (∑ ω, μ ω * Xi ω) / X := by
        simp only [Z, mul_add, Finset.sum_add_distrib, div_eq_mul_inv, Finset.sum_mul, mul_assoc]
      _ ≤ 1 + 1 := add_le_add ((div_le_one hpM).2 incidenceMoment) ((div_le_one hpX).2 groupMoment)
      _ = 2 := by norm_num
  obtain ⟨ω, hω⟩ := exists_of_mean_le μ Z mass nonneg 2 avg
  have hcell : collision (cell ω) ≤ 2 * M :=
    (div_le_iff₀ hpM).mp ((le_add_of_nonneg_right (div_nonneg (hXi ω) hpX.le)).trans hω)
  have hgroup : Xi ω ≤ 2 * X :=
    (div_le_iff₀ hpX).mp ((le_add_of_nonneg_left (div_nonneg (collision_nonneg _) hpM.le)).trans hω)
  refine ⟨ω, cell_load_of_potential _ _ hcell incidenceFeasible, fun i g => ?_⟩
  have hi : collision (assignment ω i) ≤ Xi ω :=
    Finset.single_le_sum (fun j _ => collision_nonneg (assignment ω j)) (Finset.mem_univ i)
  exact cell_load_of_potential _ _ (hi.trans hgroup) groupFeasible g

theorem appendixD_certificate_of_moment [Fintype Ω] (μ : Ω → ℚ)
    (mass : ∑ ω, μ ω = 1) (nonneg : ∀ ω, 0 ≤ μ ω) (cell : Ω → P → C) (Δ : ℚ)
    (moment : (∑ ω, μ ω * collision (cell ω)) ≤ 2 * Fintype.card P * Δ)
    (feasible : 2 * (Fintype.card C : ℚ)^2 * Δ ≤ Fintype.card P) :
    ∃ ω, CollisionCertificate (cell ω) Δ := by
  obtain ⟨ω, hω⟩ := exists_of_mean_le μ (fun ω => collision (cell ω)) mass nonneg _ moment
  exact ⟨ω, ⟨hω, feasible⟩⟩

#print axioms collision_pair
#print axioms mean_collision_le
#print axioms exists_of_mean_le
#print axioms cell_load_of_potential
#print axioms main_certificates_of_moments
#print axioms appendixD_certificate_of_moment

end S8

