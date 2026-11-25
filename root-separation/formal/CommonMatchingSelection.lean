import FiniteSelection
import IndependentThinning
import LocalVariance
import ThinningBlockBounds
import SeparatedRank

/-!
# One oriented induced matching for every listed cut

Independently mark and orient the graph edges. Calibrating the orientation
compensates for unequal block sizes and gives each retained sign the same
multiple of its prescribed mean. A finite variance bound and union bound
select a single outcome. Its signed cut statistics are the endpoint
imbalances of a genuine induced matching in the original graph.
-/

namespace CommonMatchingSelection

open scoped BigOperators

/-- Uniform lower bound on retention probability for blocks of size at most B. -/
def rate (B : ℕ) : ℚ := (1 / 2 : ℚ) ^ B

theorem rate_pos (B : ℕ) : 0 < rate B := pow_pos (by norm_num) _

section Calibration

variable {I : Type*}

/-- Edge-dependent orientation mean used before thinning. -/
def bias (B : ℕ) (blocks : I → Finset I) (b : I → ℚ) (e : I) : ℚ :=
  (rate B / IndependentThinning.retention blocks e) * b e

theorem bias_abs_le (B : ℕ) (blocks : I → Finset I) (b : I → ℚ)
    (hblocks : ∀ e, (blocks e).card ≤ B) (hb : ∀ e, |b e| ≤ 1) (e : I) :
    |bias B blocks b e| ≤ 1 := by
  have hp : 0 < IndependentThinning.retention blocks e := rate_pos _
  have hlow : rate B ≤ IndependentThinning.retention blocks e :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (hblocks e)
  have hratio : rate B / IndependentThinning.retention blocks e ≤ 1 := (div_le_one₀ hp).2 hlow
  rw [bias, abs_mul, abs_of_nonneg (div_nonneg (rate_pos B).le hp.le)]
  exact (mul_le_mul hratio (hb e) (abs_nonneg _) zero_le_one).trans_eq (by norm_num)

theorem retention_bias (B : ℕ) (blocks : I → Finset I) (b : I → ℚ) (e : I) :
    IndependentThinning.retention blocks e * bias B blocks b e = rate B * b e := by
  have hp : 0 < IndependentThinning.retention blocks e := rate_pos _
  rw [bias, ← mul_assoc, mul_div_cancel₀ _ hp.ne']

end Calibration

variable {V I J : Type*} [DecidableEq V]

/-- Natural endpoint imbalance equals the absolute difference in rational
arithmetic used by the random experiment. -/
theorem cast_endpointImbalance [Fintype I] (e : (I × Bool) ↪ V) (S : Finset V) :
    (SeparatedRank.endpointImbalance e S : ℚ) =
      |((SeparatedRank.endpointPart e S false).card : ℚ) -
        (SeparatedRank.endpointPart e S true).card| := by
  let a := (SeparatedRank.endpointPart e S false).card
  let b := (SeparatedRank.endpointPart e S true).card
  change (((a - b) + (b - a) : ℕ) : ℚ) = |(a : ℚ) - b|
  rcases le_total b a with h | h
  · rw [Nat.sub_eq_zero_of_le h, add_zero, Nat.cast_sub h,
      abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h))]
  · rw [Nat.sub_eq_zero_of_le h, zero_add, Nat.cast_sub h,
      abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr h)), neg_sub]

/-- The independent coin experiment uses exactly the retention predicate of
the graph's deterministic matching constructor. -/
theorem signedValue_eq (E : Finset (V × V)) (ω : IndependentThinning.Outcome E) (e : E) :
    MatchingThinning.signedValue E (fun f => (ω f).1) (fun f => (ω f).2) e =
      IndependentThinning.signedValue (MatchingThinning.block E) ω e := by
  classical
  unfold MatchingThinning.signedValue IndependentThinning.signedValue
  by_cases hk : e ∈ MatchingThinning.retained E (fun f => (ω f).1)
  · rw [if_pos hk]
    symm
    apply if_pos
    obtain ⟨he, hother⟩ := (MatchingThinning.keep_iff E _ e).1 hk
    intro f hf
    by_cases hfe : f = e
    · simpa [hfe] using he
    · simpa [hfe] using hother f hf hfe
  · rw [if_neg hk]
    symm
    apply if_neg
    intro hp
    apply hk ((MatchingThinning.keep_iff E _ e).2 ?_)
    refine ⟨?_, ?_⟩
    · simpa using hp e (MatchingThinning.self_mem_block E e)
    · intro f hf hfe
      simpa [hfe] using hp f hf

theorem realized_imbalance (E : Finset (V × V)) (hloop : ∀ v, (v, v) ∉ E)
    (ω : IndependentThinning.Outcome E) (S : Finset V) :
    (SeparatedRank.endpointImbalance
      (MatchingThinning.matching E hloop (fun f => (ω f).1) (fun f => (ω f).2)).endpoint S : ℚ) =
      |∑ e : E, GraphCutMoments.cutDifference ℚ S e.1 *
        IndependentThinning.signedValue (MatchingThinning.block E) ω e| := by
  rw [cast_endpointImbalance]
  change |((MatchingThinning.sideIndices _ S false).card : ℚ) - (MatchingThinning.sideIndices _ S true).card| = _
  rw [MatchingThinning.signed_imbalance E hloop (fun f => (ω f).1) (fun f => (ω f).2) S]
  simp_rw [signedValue_eq]

variable [Fintype J]

/-- All listed vertex cuts receive the required endpoint imbalance from a
single chosen pair of mark and orientation patterns. The union-bound test is
stated in finite rational arithmetic. -/
theorem select_common (E : Finset (V × V)) (hloop : ∀ v, (v, v) ∉ E)
    (B : ℕ) (hblock : ∀ e, (MatchingThinning.block E e).card ≤ B)
    (cuts : J → Finset V) (b : E → ℚ) (hb : ∀ e, |b e| ≤ 1)
    (margin : ℚ) (d : ℕ) (hmargin : 0 < margin) (hd : (d : ℚ) ≤ margin)
    (hmean : ∀ j, 2 * margin ≤ rate B *
      |∑ e : E, b e * GraphCutMoments.cutDifference ℚ (cuts j) e.1|)
    (hbudget : (Fintype.card J : ℚ) * ((4 * (E.card : ℚ) * (B * B : ℕ)) / margin ^ 2) < 1) :
    ∃ mark orientation : E → Bool, ∀ j,
      d ≤ SeparatedRank.endpointImbalance (MatchingThinning.matching E hloop mark orientation).endpoint
        (cuts j) := by
  classical
  let blocks := MatchingThinning.block E
  let w := bias B blocks b
  let μ := IndependentThinning.prob w
  let Z := fun e (ω : IndependentThinning.Outcome E) => IndependentThinning.signedValue blocks ω e
  let c := fun j (e : E) => GraphCutMoments.cutDifference ℚ (cuts j) e.1
  let Y := fun j ω => ∑ e : E, c j e * Z e ω
  let a := fun j => rate B * ∑ e : E, b e * c j e
  let variance : ℚ := 4 * (E.card : ℚ) * (B * B : ℕ)
  have hμ : ∀ ω, 0 ≤ μ ω := IndependentThinning.prob_nonneg w (bias_abs_le B blocks b hblock hb)
  have hmass : ∑ ω, μ ω = 1 := IndependentThinning.sum_prob w
  have hfirst (e : E) : LocalVariance.mean μ (Z e) = rate B * b e :=
    (IndependentThinning.mean_signedValue w blocks e (MatchingThinning.self_mem_block E e)).trans
      (retention_bias B blocks b e)
  have hcenter (j : J) : (∑ e : E, c j e * LocalVariance.mean μ (Z e)) = a j := by
    simp only [hfirst, a, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  have hmom (j : J) : (∑ ω, μ ω * (Y j ω - a j) ^ 2) ≤ variance := by
    rw [← hcenter]
    have hv := LocalVariance.variance_of_disjoint_blocks μ Z (c j) blocks B hμ hmass
      (fun e ω => IndependentThinning.abs_signedValue_le_one blocks ω e)
      (fun e => GraphCutMoments.abs_cutDifference_le_one (cuts j) e.1)
      (fun e f => (ThinningBlockBounds.mem_block_symm E e f).mp) hblock
      (fun e f hdis => IndependentThinning.disjoint_cross_moment w blocks e f
        (MatchingThinning.self_mem_block E e) (MatchingThinning.self_mem_block E f) hdis)
    simpa only [Fintype.card_coe] using hv
  have hlarge (j : J) : 2 * margin ≤ |a j| := by
    simpa only [a, c, abs_mul, abs_of_nonneg (rate_pos B).le] using hmean j
  have hbudget' : (∑ _j : J, variance / margin ^ 2) < 1 := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hbudget
  obtain ⟨ω, _, hall⟩ := FiniteSelection.exists_simultaneous_large μ Y a
    (fun _ => margin) (fun _ => variance) hμ hmass (fun _ => hmargin) hmom hbudget' hlarge
  refine ⟨fun e => (ω e).1, fun e => (ω e).2, ?_⟩
  intro j
  apply (Nat.cast_le (α := ℚ)).mp
  rw [realized_imbalance E hloop ω (cuts j)]
  exact hd.trans (hall j).le

/-- Maximum graph degree D supplies the uniform bound (2D)² on the actual
conflict blocks of the graph edges. -/
theorem select_degree (E : Finset (V × V)) (hloop : ∀ v, (v, v) ∉ E)
    (D : ℕ) (hdeg : ∀ v, GraphCutMoments.degree E v ≤ D)
    (cuts : J → Finset V) (b : E → ℚ) (hb : ∀ e, |b e| ≤ 1)
    (margin : ℚ) (d : ℕ) (hmargin : 0 < margin) (hd : (d : ℚ) ≤ margin)
    (hmean : ∀ j, 2 * margin ≤ rate ((2 * D) ^ 2) *
      |∑ e : E, b e * GraphCutMoments.cutDifference ℚ (cuts j) e.1|)
    (hbudget : (Fintype.card J : ℚ) *
      ((4 * (E.card : ℚ) * (((2 * D) ^ 2 * (2 * D) ^ 2 : ℕ) : ℚ)) / margin ^ 2) < 1) :
    ∃ mark orientation : E → Bool, ∀ j,
      d ≤ SeparatedRank.endpointImbalance (MatchingThinning.matching E hloop mark orientation).endpoint
        (cuts j) :=
  select_common E hloop ((2 * D) ^ 2) (ThinningBlockBounds.block_card_le E D hdeg)
    cuts b hb margin d hmargin hd hmean hbudget

#print axioms rate_pos
#print axioms bias_abs_le
#print axioms retention_bias
#print axioms cast_endpointImbalance
#print axioms signedValue_eq
#print axioms realized_imbalance
#print axioms select_common
#print axioms select_degree

end CommonMatchingSelection
