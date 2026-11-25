import HuberEdgeCorrelation
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The endpoint-incidence double count and the vertex-to-edge second-moment
transfer used in the direct edge argument of Appendix B. -/

namespace GraphCutMoments

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An unoriented incidence count for a finite set of stored oriented edges. -/
def degree (E : Finset (V × V)) (v : V) : ℕ :=
  (E.filter fun e => e.1 = v).card + (E.filter fun e => e.2 = v).card

private theorem endpoint_sum {R : Type*} [CommSemiring R] (E : Finset (V × V))
    (p : V × V → V) (f : V → R) :
    ∑ e ∈ E, f (p e) = ∑ v, ((E.filter fun e => p e = v).card : R) * f v := by
  simpa only [Finset.sum_const, nsmul_eq_mul] using (Finset.sum_fiberwise' E p f).symm

theorem weighted_incidence {R : Type*} [CommSemiring R] (E : Finset (V × V)) (f : V → R) :
    (∑ e ∈ E, (f e.1 + f e.2)) = ∑ v, (degree E v : R) * f v := by
  rw [Finset.sum_add_distrib, endpoint_sum E Prod.fst f, endpoint_sum E Prod.snd f]
  simp only [degree, Nat.cast_add, add_mul, Finset.sum_add_distrib]

theorem sum_degree (E : Finset (V × V)) : (∑ v, degree E v) = 2 * E.card := by
  simpa [Nat.mul_comm] using (weighted_incidence E (fun _ => (1 : ℕ))).symm

theorem regular_edge_count (E : Finset (V × V)) (d : ℕ) (hreg : ∀ v, degree E v = d) :
    2 * E.card = d * Fintype.card V := by
  rw [← sum_degree]
  simp [hreg, Nat.mul_comm]

/-- The stored edges with exactly one endpoint in a given vertex subset. -/
def boundary (E : Finset (V × V)) (S : Finset V) : Finset (V × V) :=
  E.filter fun e => ¬ (e.1 ∈ S ↔ e.2 ∈ S)

def cutBit (R : Type*) [Zero R] [One R] (S : Finset V) (v : V) : R :=
  if v ∈ S then 1 else 0

def cutDifference (R : Type*) [Ring R] (S : Finset V) (e : V × V) : R :=
  cutBit R S e.1 - cutBit R S e.2

omit [Fintype V] in
theorem cut_energy_eq_boundary {R : Type*} [Ring R] (E : Finset (V × V)) (S : Finset V) :
    (∑ e ∈ E, (cutDifference R S e) ^ 2) = ((boundary E S).card : R) := by
  rw [boundary, Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases hu : e.1 ∈ S <;> by_cases hv : e.2 ∈ S <;> simp [cutDifference, cutBit, hu, hv]

section Moments

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

omit [Fintype V] in
theorem abs_cutDifference_le_one (S : Finset V) (e : V × V) :
    |cutDifference R S e| ≤ 1 := by
  by_cases hu : e.1 ∈ S <;> by_cases hv : e.2 ∈ S <;> simp [cutDifference, cutBit, hu, hv]

theorem edge_energy_le (E : Finset (V × V)) (D : ℕ) (hdeg : ∀ v, degree E v ≤ D)
    (Y : V → R) :
    (∑ e ∈ E, (Y e.1 - Y e.2) ^ 2) ≤ 2 * D * ∑ v, (Y v) ^ 2 := by
  calc
    _ ≤ ∑ e ∈ E, 2 * ((Y e.1) ^ 2 + (Y e.2) ^ 2) := by
      apply Finset.sum_le_sum
      intro e _
      nlinarith only [sq_nonneg (Y e.1 + Y e.2)]
    _ = 2 * ∑ v, (degree E v : R) * (Y v) ^ 2 := by
      rw [← Finset.mul_sum, weighted_incidence E (fun v => (Y v) ^ 2)]
    _ ≤ 2 * ∑ v, (D : R) * (Y v) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ zero_le_two
      apply Finset.sum_le_sum
      intro v _
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hdeg v)) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum, mul_assoc]

/-- Uniform edge and vertex second moments on any nonempty positive-regular graph. -/
theorem regular_mean_energy_le (E : Finset (V × V)) (d : ℕ) (hd : 0 < d)
    (hV : 0 < Fintype.card V) (hreg : ∀ v, degree E v = d) (Y : V → R) :
    (∑ e ∈ E, (Y e.1 - Y e.2) ^ 2) / (E.card : R) ≤
      4 * ((∑ v, (Y v) ^ 2) / (Fintype.card V : R)) := by
  have hc := regular_edge_count E d hreg
  have hE : 0 < E.card := by
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h, mul_zero] at hc
    exact (Nat.mul_pos hd hV).ne' hc.symm
  have heR : (0 : R) < E.card := by exact_mod_cast hE
  have hvR : (0 : R) < Fintype.card V := by exact_mod_cast hV
  have hcR : (2 : R) * E.card = (d : R) * Fintype.card V := by exact_mod_cast hc
  have hratio : (2 : R) * d / E.card = 4 / Fintype.card V := by
    apply (div_eq_div_iff heR.ne' hvR.ne').2
    linarith only [hcR]
  calc
    _ ≤ (2 * (d : R) * ∑ v, (Y v) ^ 2) / E.card :=
      (div_le_div_iff_of_pos_right heR).2 (edge_energy_le E d (fun v => (hreg v).le) Y)
    _ = (2 * (d : R) / E.card) * ∑ v, (Y v) ^ 2 := by ring
    _ = _ := by rw [hratio]; ring

theorem cubic_mean_energy_le [Nonempty V] (E : Finset (V × V))
    (hreg : ∀ v, degree E v = 3) (Y : V → R) :
    (∑ e ∈ E, (Y e.1 - Y e.2) ^ 2) / (E.card : R) ≤
      4 * ((∑ v, (Y v) ^ 2) / (Fintype.card V : R)) :=
  regular_mean_energy_le E 3 (by decide) Fintype.card_pos hreg Y

/-- Apply the cubic estimate directly to a signed sum of vertex functions and
the corresponding linear combination of their oriented edge differences. -/
theorem cubic_signed_edge_moment [Nonempty V] {J : Type*} [Fintype J]
    (E : Finset (V × V)) (hreg : ∀ v, degree E v = 3)
    (a : J → R) (f : J → V → R) (H : R)
    (hmoment : (∑ v, (∑ j, a j * f j v) ^ 2) / (Fintype.card V : R) ≤ H ^ 2) :
    (∑ e ∈ E, (∑ j, a j * (f j e.1 - f j e.2)) ^ 2) / (E.card : R) ≤ (2 * H) ^ 2 := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  exact (cubic_mean_energy_le E hreg (fun v => ∑ j, a j * f j v)).trans
    (by nlinarith only [hmoment])

end Moments

/-- A single rational edge weighting correlates with every prescribed cut of
a cubic graph. Inputs are the actual boundary densities and a signed second
moment on vertices. The latter may center each indicator by its own constant. -/
theorem cubic_cut_correlations [Nonempty V] {J : Type*} [Fintype J]
    (E : Finset (V × V)) (hreg : ∀ v, degree E v = 3)
    (S : J → Finset V) (center : J → ℚ) (p A : ℚ) (hp : 0 < p) (hp1 : p ≤ 1)
    (hA : 1 ≤ A) (hboundary : ∀ i, p ≤ ((boundary E (S i)).card : ℚ) / E.card)
    (hmoment : ∀ eps : J → Bool,
      (∑ v, (BangCore.signedTotal (fun i w => cutBit ℚ (S i) w - center i) eps v) ^ 2) /
        (Fintype.card V : ℚ) ≤ A ^ 2) :
    ∃ b : E → ℚ, (∀ e, |b e| ≤ 1) ∧ ∀ i,
      3 * p ^ 2 / (32 * A) ≤ |(∑ e : E, b e * cutDifference ℚ (S i) e.1) / E.card| := by
  let g (i : J) (e : E) := cutDifference ℚ (S i) e.1
  let f (i : J) (v : V) := cutBit ℚ (S i) v - center i
  let μ (_e : E) := 1 / (E.card : ℚ)
  have uniform (t : E → ℚ) : (∑ e, μ e * t e) = (∑ e, t e) / E.card := by
    simp only [μ, ← Finset.mul_sum]
    ring
  have hd (i : J) (e : V × V) : f i e.1 - f i e.2 = cutDifference ℚ (S i) e := by
    simp only [f, cutDifference]
    ring
  have energy (i : J) : p ≤ ∑ e, μ e * (g i e) ^ 2 := by
    rw [uniform]
    change p ≤ (∑ e : E, (cutDifference ℚ (S i) e.1) ^ 2) / E.card
    rw [Finset.sum_coe_sort E (fun e => (cutDifference ℚ (S i) e) ^ 2), cut_energy_eq_boundary]
    exact hboundary i
  have moment (eps : J → Bool) :
      (∑ e, μ e * (BangCore.signedTotal g eps e) ^ 2) ≤ (2 * A) ^ 2 := by
    rw [uniform]
    change (∑ e : E, (∑ i, BangCore.bitSign (eps i) * cutDifference ℚ (S i) e.1) ^ 2) /
      E.card ≤ (2 * A) ^ 2
    rw [Finset.sum_coe_sort E (fun e =>
      (∑ i, BangCore.bitSign (eps i) * cutDifference ℚ (S i) e) ^ 2)]
    have h := cubic_signed_edge_moment E hreg (fun i => BangCore.bitSign (eps i)) f A (hmoment eps)
    simpa only [hd] using h
  obtain ⟨b, hb, hc⟩ := HuberEdgeCorrelation.exists_edge_correlation_of_doubled_bound μ g p A
    (fun _ => div_nonneg zero_le_one (Nat.cast_nonneg _)) hp hp1 hA
    (fun i e => abs_cutDifference_le_one (S i) e.1) energy moment
  refine ⟨b, hb, fun i => ?_⟩
  simpa only [mul_assoc, uniform, g] using hc i

/-- Expansion and sign-mass balance supply the boundary energy. The conclusion
uses an unnormalized sum over the original oriented edge set. -/
theorem cubic_expander_cut_correlations [Nonempty V] {J : Type*} [Fintype J]
    (E : Finset (V × V)) (hreg : ∀ v, degree E v = 3)
    (S : J → Finset V) (center : J → ℚ) (γ η A : ℚ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hη : 0 < η) (hη1 : η ≤ 1 / 2) (hA : 1 ≤ A)
    (hexpand : ∀ T : Finset V,
      γ * (min T.card (Fintype.card V - T.card) : ℕ) ≤ ((boundary E T).card : ℚ))
    (hbalance : ∀ i, η * Fintype.card V ≤ (min (S i).card (Fintype.card V - (S i).card) : ℕ))
    (hmoment : ∀ eps : J → Bool,
      (∑ v, (BangCore.signedTotal (fun i w => cutBit ℚ (S i) w - center i) eps v) ^ 2) /
        (Fintype.card V : ℚ) ≤ A ^ 2) :
    ∃ b : E → ℚ, (∀ e, |b e| ≤ 1) ∧ ∀ i,
      γ ^ 2 * η ^ 2 * Fintype.card V / (16 * A) ≤ |∑ e : E, b e * cutDifference ℚ (S i) e.1| := by
  have hc : 2 * (E.card : ℚ) = 3 * Fintype.card V := by exact_mod_cast regular_edge_count E 3 hreg
  have hv : 0 < (Fintype.card V : ℚ) := by exact_mod_cast Fintype.card_pos (α := V)
  have he : 0 < (E.card : ℚ) := by linarith only [hc, hv]
  have heq : (E.card : ℚ) = 3 * Fintype.card V / 2 := by linarith only [hc]
  have hp : 0 < 2 * γ * η / 3 := by positivity
  have hp1 : 2 * γ * η / 3 ≤ 1 := by
    linarith only [mul_le_mul hγ1 hη1 hη.le zero_le_one]
  have hbnd (i : J) : 2 * γ * η / 3 ≤ ((boundary E (S i)).card : ℚ) / E.card := by
    apply (le_div_iff₀ he).2
    calc
      _ = γ * (η * Fintype.card V) := by rw [heq]; ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left (hbalance i) hγ.le).trans (hexpand (S i))
  obtain ⟨b, hb, corr⟩ := cubic_cut_correlations E hreg S center (2 * γ * η / 3) A
    hp hp1 hA hbnd hmoment
  refine ⟨b, hb, fun i => ?_⟩
  have hh := corr i
  rw [abs_div, abs_of_pos he, le_div_iff₀ he] at hh
  calc
    _ = (3 * (2 * γ * η / 3) ^ 2 / (32 * A)) * E.card := by
      rw [heq]
      field_simp [ne_of_gt (zero_lt_one.trans_le hA)]
      ring
    _ ≤ _ := hh

#print axioms weighted_incidence
#print axioms sum_degree
#print axioms regular_edge_count
#print axioms cut_energy_eq_boundary
#print axioms abs_cutDifference_le_one
#print axioms edge_energy_le
#print axioms regular_mean_energy_le
#print axioms cubic_mean_energy_le
#print axioms cubic_signed_edge_moment
#print axioms cubic_cut_correlations
#print axioms cubic_expander_cut_correlations

end GraphCutMoments
