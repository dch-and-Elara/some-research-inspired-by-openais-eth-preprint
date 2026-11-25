import ExpanderBarrier
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Sqrt

/-!
# An explicit finite exponent for the cubic expander barrier

Write t for the geometric constant and N for the number of vertices. The
margin is tN/H. Cubic edge counting turns the union-bound budget into
N > 7776 k H² / t². Taking the natural floor gives one actual exponent for
the theorem on the correctly reduced final output.
-/

namespace FiniteGrowth

open scoped BigOperators

/-- Rounding a margin of at least two loses at most a factor of two. -/
theorem floor_bounds (x : ℚ) (hx : 2 ≤ x) :
    x / 2 ≤ (⌊x⌋₊ : ℚ) ∧ (⌊x⌋₊ : ℚ) ≤ x := by
  have hlt := Nat.lt_floor_add_one x
  exact ⟨by linarith, Nat.floor_le (by linarith)⟩

/-- The exact rational budget after using the cubic identity 2M = 3N. -/
theorem cubic_budget_iff (N M k H t : ℚ) (hN : 0 < N) (hH : 0 < H)
    (ht : 0 < t) (hM : 2 * M = 3 * N) :
    k * ((4 * M * 1296) / (t * N / H) ^ 2) < 1 ↔
      7776 * k * H ^ 2 / t ^ 2 < N := by
  have hratio : 4 * M * 1296 / (t * N / H) ^ 2 = 7776 * H ^ 2 / (t ^ 2 * N) := by
    rw [show M = 3 * N / 2 by linarith]
    field_simp [hN.ne', hH.ne', ht.ne']
    ring
  rw [hratio, ← mul_div_assoc, div_lt_one₀ (mul_pos (sq_pos_of_pos ht) hN),
    div_lt_iff₀ (sq_pos_of_pos ht)]
  ring_nf

/-- A linear cap on both menu size and scale squared reduces the finite
threshold to a constant times the square of the coordinate count u. -/
theorem threshold_of_linear_caps (N k H t u k₀ h₀ : ℚ) (ht : 0 < t)
    (hk : 0 ≤ k) (hmenu : k ≤ k₀ * u) (hscale : H ^ 2 ≤ h₀ * u)
    (hthreshold : 7776 * k₀ * h₀ * u ^ 2 < N * t ^ 2) :
    7776 * k * H ^ 2 / t ^ 2 < N := by
  apply (div_lt_iff₀ (sq_pos_of_pos ht)).2
  calc
    _ = 7776 * (k * H ^ 2) := by ring
    _ ≤ 7776 * ((k₀ * u) * (h₀ * u)) := mul_le_mul_of_nonneg_left
      (mul_le_mul hmenu hscale (sq_nonneg H) (hk.trans hmenu)) (by norm_num)
    _ = 7776 * k₀ * h₀ * u ^ 2 := by ring
    _ < _ := hthreshold

/-- A positive integral scale for use when the original second-moment
estimate has integral right-hand side s. -/
def integerScale (s : ℕ) : ℕ := s.sqrt + 1

theorem integerScale_bounds (s : ℕ) (hs : 0 < s) :
    1 ≤ integerScale s ∧ s ≤ integerScale s ^ 2 ∧ integerScale s ^ 2 ≤ 4 * s := by
  have hr : 0 < s.sqrt := Nat.sqrt_pos.mpr hs
  have hscale : integerScale s ≤ 2 * s.sqrt := by unfold integerScale; omega
  refine ⟨by unfold integerScale; omega, (Nat.lt_succ_sqrt' s).le, ?_⟩
  calc
    _ ≤ (2 * s.sqrt) ^ 2 := Nat.pow_le_pow_left hscale _
    _ = 4 * s.sqrt ^ 2 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.sqrt_le' s)

/-- The constant multiplying N/H in the selected exponent's unrounded margin. -/
def coefficient (γ η : ℚ) : ℚ := CommonMatchingSelection.rate 36 * γ ^ 2 * η ^ 2 / 32

theorem coefficient_pos {γ η : ℚ} (hγ : 0 < γ) (hη : 0 < η) : 0 < coefficient γ η := by
  have hrate := CommonMatchingSelection.rate_pos 36
  unfold coefficient
  positivity

theorem coefficient_le_one {γ η : ℚ} (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (hη : 0 ≤ η) (hη1 : η ≤ 1) :
    coefficient γ η ≤ 1 := by
  have hr : CommonMatchingSelection.rate 36 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hg : γ ^ 2 ≤ 1 := pow_le_one₀ hγ hγ1
  have he : η ^ 2 ≤ 1 := pow_le_one₀ hη hη1
  have hprod := mul_le_mul (mul_le_mul hr hg (sq_nonneg _) zero_le_one) he
    (sq_nonneg _) (by norm_num : (0 : ℚ) ≤ 1 * 1)
  unfold coefficient
  apply (div_le_one₀ (by norm_num : (0 : ℚ) < 32)).2
  linarith only [hprod]

variable {V I A J T R S K : Type*}
variable [Fintype V] [DecidableEq V] [Nonempty V]
variable [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Nonempty A]
variable [Fintype J]
variable {E : Finset (V × V)} {L : V → I → A} {owner : J → I} {symbols : J → Finset A}

omit [Nonempty V] [Nonempty A] in
theorem margin_eq (G : ExpanderBarrier.LabelGeometry E L owner symbols) :
    ExpanderBarrier.margin G = coefficient G.gamma G.eta * Fintype.card V / G.H := by
  unfold ExpanderBarrier.margin coefficient
  ring

omit [Nonempty A] in
/-- The exact threshold for the composed geometric theorem. -/
theorem selection_budget_iff (G : ExpanderBarrier.LabelGeometry E L owner symbols) :
    ExpanderBarrier.SelectionBudget G ↔
      7776 * (Fintype.card J : ℚ) * G.H ^ 2 / (coefficient G.gamma G.eta) ^ 2 < Fintype.card V := by
  have hc := GraphCutMoments.regular_edge_count E 3 G.regular
  have hM : 2 * (E.card : ℚ) = 3 * (Fintype.card V : ℚ) := by exact_mod_cast hc
  have hN : 0 < (Fintype.card V : ℚ) := by exact_mod_cast Fintype.card_pos (α := V)
  unfold ExpanderBarrier.SelectionBudget
  rw [margin_eq]
  exact cubic_budget_iff _ _ _ _ _ hN (zero_lt_one.trans_le G.H_ge_one)
    (coefficient_pos G.gamma_pos G.eta_pos) hM

omit [Nonempty V] [Nonempty A] in
/-- For a nonempty menu, the same threshold already ensures the margin is at
least two. This eliminates an independent rounding assumption. -/
theorem margin_ge_two_of_threshold [Nonempty J] (G : ExpanderBarrier.LabelGeometry E L owner symbols)
    (hsize : 7776 * (Fintype.card J : ℚ) * G.H ^ 2 / (coefficient G.gamma G.eta) ^ 2 <
      Fintype.card V) :
    2 ≤ ExpanderBarrier.margin G := by
  let t := coefficient G.gamma G.eta
  have ht : 0 < t := coefficient_pos G.gamma_pos G.eta_pos
  have ht1 : t ≤ 1 := coefficient_le_one G.gamma_pos.le G.gamma_le_one G.eta_pos.le
    (by linarith only [G.eta_le_half])
  have hH : 0 < G.H := zero_lt_one.trans_le G.H_ge_one
  have hK : 1 ≤ (Fintype.card J : ℚ) := by exact_mod_cast Fintype.card_pos (α := J)
  have hKH : G.H ≤ (Fintype.card J : ℚ) * G.H := le_mul_of_one_le_left hH.le hK
  have hs : 2 * t ≤ 7776 * (Fintype.card J : ℚ) * G.H := by
    nlinarith only [ht1, G.H_ge_one, hKH]
  have hsmall : 2 * G.H / t ≤ 7776 * (Fintype.card J : ℚ) * G.H ^ 2 / t ^ 2 := by
    apply (div_le_div_iff₀ ht (sq_pos_of_pos ht)).2
    calc
      _ = (2 * t) * (G.H * t) := by ring
      _ ≤ (7776 * (Fintype.card J : ℚ) * G.H) * (G.H * t) :=
        mul_le_mul_of_nonneg_right hs (mul_nonneg hH.le ht.le)
      _ = _ := by ring
  have htwo := (div_le_iff₀ ht).mp (hsmall.trans hsize.le)
  rw [margin_eq, le_div_iff₀ hH, mul_comm (coefficient G.gamma G.eta)]
  exact htwo

omit [Nonempty A] in
/-- Choosing the actual integer exponent by flooring the verified margin
provides a proportional lower bound and all inputs to the rank barrier. -/
theorem finite_exponent [Nonempty J] (G : ExpanderBarrier.LabelGeometry E L owner symbols)
    (hsize : 7776 * (Fintype.card J : ℚ) * G.H ^ 2 / (coefficient G.gamma G.eta) ^ 2 <
      Fintype.card V) :
    coefficient G.gamma G.eta * Fintype.card V / (2 * G.H) ≤ (⌊ExpanderBarrier.margin G⌋₊ : ℚ) ∧
      (⌊ExpanderBarrier.margin G⌋₊ : ℚ) ≤ ExpanderBarrier.margin G ∧
      ExpanderBarrier.SelectionBudget G := by
  obtain ⟨hl, hu⟩ := floor_bounds _ (margin_ge_two_of_threshold G hsize)
  refine ⟨?_, hu, (selection_budget_iff G).2 hsize⟩
  calc
    _ = ExpanderBarrier.margin G / 2 := by rw [margin_eq]; ring
    _ ≤ _ := hl

variable [Fintype T] [CommRing R] [CommRing S] [Nontrivial S] [Field K]

/-- A final integral-output representation satisfying the residue contract
has at least two to the explicit floored exponent terms. -/
theorem modular_growth_barrier [Nonempty J] (G : ExpanderBarrier.LabelGeometry E L owner symbols)
    (hsize : 7776 * (Fintype.card J : ℚ) * G.H ^ 2 / (coefficient G.gamma G.eta) ^ 2 <
      Fintype.card V)
    (embed : R →+* K) (residue : R →+* S) (hinjective : Function.Injective embed)
    (output : (V → Bool) → R) (terms : T → SeparatedRank.VertexTerm V K) (assigned : T → J)
    (hside : ∀ t, (terms t).side = EmpiricalCutMoments.labelCut L owner symbols (assigned t))
    (hrepresentation : ∀ σ, embed (output σ) = ∑ t, (terms t).value σ)
    (hcorrect : ∀ σ, residue (output σ) = (PinnedCNF.modelCount (PinnedCNF.formula E σ) : S)) :
    coefficient G.gamma G.eta * Fintype.card V / (2 * G.H) ≤ (⌊ExpanderBarrier.margin G⌋₊ : ℚ) ∧
      2 ^ ⌊ExpanderBarrier.margin G⌋₊ ≤ Fintype.card T := by
  obtain ⟨hl, hu, hb⟩ := finite_exponent G hsize
  exact ⟨hl, ExpanderBarrier.modular_output_barrier G _ hu hb embed residue hinjective
    output terms assigned hside hrepresentation hcorrect⟩

#print axioms floor_bounds
#print axioms cubic_budget_iff
#print axioms threshold_of_linear_caps
#print axioms integerScale_bounds
#print axioms coefficient_pos
#print axioms coefficient_le_one
#print axioms margin_eq
#print axioms selection_budget_iff
#print axioms margin_ge_two_of_threshold
#print axioms finite_exponent
#print axioms modular_growth_barrier

end FiniteGrowth
