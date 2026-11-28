import J2R47ExpectedMarkov
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

set_option autoImplicit false
set_option warningAsError true

namespace J2R119Probability

open scoped BigOperators ENNReal NNReal
open MeasureTheory FiniteWeightedQueryTree J2R45BoundedError J2R47Expected

noncomputable section

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- The probability of a seed event as a real number. -/
def probability (μ : Measure Seed) (s : Set Seed) : ℝ := (μ s).toReal

def cutoff (budget : ℝ≥0) : ℕ := ⌊12 * (budget : ℝ)⌋₊

theorem cutoff_le (budget : ℝ≥0) : (cutoff budget : ℝ) ≤ 12 * (budget : ℝ) := by
  exact Nat.floor_le (by positivity)

theorem exponent_bound (budget : ℝ≥0) (exponent : ℕ)
    (h : (2 : ℕ)^exponent ≤ 6 * cutoff budget) :
    (2 : ℝ)^exponent / 72 ≤ (budget : ℝ) := by
  have hcast : (2 : ℝ)^exponent ≤ 6 * (cutoff budget : ℝ) := by exact_mod_cast h
  linarith [cutoff_le budget]

theorem bad_probability (μ : Measure Seed) [IsProbabilityMeasure μ]
    (cost : Seed → ℕ) (budget : ℝ≥0)
    (hcost : AEMeasurable (fun i => (cost i : ℝ≥0∞)) μ)
    (hmean : (∫⁻ i, (cost i : ℝ≥0∞) ∂μ) ≤ (budget : ℝ≥0∞)) :
    probability μ {i | cutoff budget < cost i} ≤ 1/12 := by
  let T := cutoff budget
  have hset : {i | (↑(T+1) : ℝ≥0∞) ≤ (cost i : ℝ≥0∞)} = {i | T < cost i} := by
    ext i
    change ((↑(T+1) : ℝ≥0∞) ≤ (cost i : ℝ≥0∞)) ↔ T < cost i
    rw [← Nat.succ_le_iff]
    exact_mod_cast (Iff.rfl : T+1 ≤ cost i ↔ T+1 ≤ cost i)
  have h := (mul_meas_ge_le_lintegral₀ hcost (↑(T+1) : ℝ≥0∞)).trans hmean
  rw [hset] at h
  have hp : ((T : ℝ)+1) * probability μ {i | T < cost i} ≤ (budget : ℝ) := by
    simpa only [probability, ENNReal.toReal_mul, ENNReal.toReal_natCast, Nat.cast_add,
      Nat.cast_one, ENNReal.coe_toReal] using ENNReal.toReal_mono ENNReal.coe_ne_top h
  have hT : 12 * (budget : ℝ) < (T : ℝ)+1 := Nat.lt_floor_add_one _
  by_contra! hbad
  have hmul := mul_lt_mul_of_pos_left hbad (show 0 < (T : ℝ)+1 by positivity)
  linarith

def kept (good : Set Seed) (cost : Seed → ℕ) (T : ℕ) : Set Seed :=
  good ∩ {i | cost i ≤ T}

theorem kept_measurable (μ : Measure Seed) {good : Set Seed} {cost : Seed → ℕ} (T : ℕ)
    (hg : NullMeasurableSet good μ)
    (hc : AEMeasurable (fun i => (cost i : ℝ≥0∞)) μ) :
    NullMeasurableSet (kept good cost T) μ := by
  apply hg.inter
  have he : {i | (cost i : ℝ≥0∞) ≤ (T : ℝ≥0∞)} = {i | cost i ≤ T} := by
    ext i
    change ((cost i : ℝ≥0∞) ≤ (T : ℝ≥0∞)) ↔ cost i ≤ T
    exact_mod_cast (Iff.rfl : cost i ≤ T ↔ cost i ≤ T)
  rw [← he]
  exact nullMeasurableSet_le hc (aemeasurable_const (b := (T : ℝ≥0∞)))

/-- Keeping successful runs within the cutoff avoids any measurability
requirement on the output after truncation of an over-budget run. -/
theorem kept_probability (μ : Measure Seed) [IsProbabilityMeasure μ]
    (good : Set Seed) (cost : Seed → ℕ) (budget : ℝ≥0)
    (hcost : AEMeasurable (fun i => (cost i : ℝ≥0∞)) μ)
    (hmean : (∫⁻ i, (cost i : ℝ≥0∞) ∂μ) ≤ (budget : ℝ≥0∞))
    (hgood : (2:ℝ)/3 ≤ probability μ good) :
    (7:ℝ)/12 ≤ probability μ (kept good cost (cutoff budget)) := by
  let K := kept good cost (cutoff budget)
  let bad : Set Seed := {i | cutoff budget < cost i}
  have hsub : good ⊆ K ∪ bad := by
    intro i hi
    rcases le_or_gt (cost i) (cutoff budget) with h | h
    · exact Or.inl ⟨hi,h⟩
    · exact Or.inr h
  have hu := (measure_mono (μ := μ) hsub).trans (measure_union_le K bad)
  have hle : probability μ good ≤ probability μ K + probability μ bad :=
    ENNReal.toReal_le_add hu (measure_lt_top μ K).ne (measure_lt_top μ bad).ne
  linarith [bad_probability μ cost budget hcost hmean]

variable {Q R W : Type*}

/-- Success uses the required decision bit on the original oracle path. -/
def goodSeeds (oracle : Q → R) (trees : Seed → DecisionTree Q R) (target : Bool) : Set Seed :=
  {i | evaluate oracle (trees i) = target}

def paidCount (counted : Q → Bool) (oracle : Q → R)
    (trees : Seed → DecisionTree Q R) (i : Seed) : ℕ :=
  paid (mainCharge counted) oracle (trees i)

def expectedPaid (μ : Measure Seed) (counted : Q → Bool) (oracle : Q → R)
    (trees : Seed → DecisionTree Q R) : ℝ≥0∞ :=
  ∫⁻ i, (paidCount counted oracle trees i : ℝ≥0∞) ∂μ

/-- Integrate the fixed-seed bound over an arbitrary seed law. The finite
sum is over the two actual inputs per promised word. -/
theorem capacity_at_probability_cutoff [DecidableEq W]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (zero : R)
    (oracle : W → Bool → Q → R) (support : Q → Finset W)
    (off : ∀ w b q, w ∉ support q → oracle w b q = zero)
    (counted : Q → Bool) (freeConstant : ∀ w b q, counted q = false → oracle w b q = zero)
    (capacity : ℕ) (cap : ∀ q, (support q).card ≤ capacity)
    (trees : Seed → DecisionTree Q R) (pool : Finset W) (budget : ℝ≥0)
    (measCost : ∀ w ∈ pool, ∀ b, AEMeasurable
      (fun i => (paidCount counted (oracle w b) trees i : ℝ≥0∞)) μ)
    (measSuccess : ∀ w ∈ pool, ∀ b, NullMeasurableSet (goodSeeds (oracle w b) trees b) μ)
    (mean : ∀ w ∈ pool, ∀ b, expectedPaid μ counted (oracle w b) trees ≤ (budget : ℝ≥0∞))
    (success : ∀ w ∈ pool, ∀ b, (2:ℝ)/3 ≤ probability μ (goodSeeds (oracle w b) trees b)) :
    pool.card ≤ 6 * (capacity * cutoff budget) := by
  classical
  let T := cutoff budget
  let pairs := pool ×ˢ (Finset.univ : Finset Bool)
  let event (p : W × Bool) :=
    kept (goodSeeds (oracle p.1 p.2) trees p.2) (paidCount counted (oracle p.1 p.2) trees) T
  let flag (p : W × Bool) := (event p).indicator (fun _ : Seed => (1 : ℝ≥0∞))
  have hp (p : W × Bool) (h : p ∈ pairs) : p.1 ∈ pool := (Finset.mem_product.mp h).1
  have hm (p : W × Bool) (h : p ∈ pairs) : NullMeasurableSet (event p) μ :=
    kept_measurable μ T (measSuccess _ (hp p h) _) (measCost _ (hp p h) _)
  have hl (p : W × Bool) (h : p ∈ pairs) : (7:ℝ)/12 ≤ probability μ (event p) :=
    kept_probability μ _ _ budget (measCost _ (hp p h) _) (mean _ (hp p h) _) (success _ (hp p h) _)
  have hpoint (i : Seed) : (∑ p ∈ pairs, flag p i) ≤ (↑(pool.card + capacity*T) : ℝ≥0∞) := by
    let ct := clipped zero counted T (trees i)
    let wins (p : W × Bool) : ℕ := if evaluate (oracle p.1 p.2) ct = p.2 then 1 else 0
    have hflag (p : W × Bool) : flag p i ≤ (wins p : ℝ≥0∞) := by
      by_cases hi : i ∈ event p
      · have hy : evaluate (oracle p.1 p.2) (trees i) = p.2 := hi.1
        have hc : paidCount counted (oracle p.1 p.2) trees i ≤ T := hi.2
        have he := clipped_agrees_on_actual_path zero counted (oracle p.1 p.2)
          (freeConstant p.1 p.2) T (trees i) hc
        have hw : evaluate (oracle p.1 p.2) ct = p.2 := he.trans hy
        simp [flag,Set.indicator_of_mem hi,wins,hw]
      · simp [flag,Set.indicator_of_notMem hi]
    have hsum : (∑ p ∈ pairs, wins p) = ∑ w ∈ pool, pairScore ct oracle w := by
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro w _
      rw [Fintype.sum_bool]
      simp only [wins,pairScore,add_comm]
    have hT : paid (fun _ => capacity) (fun _ => zero) ct ≤ capacity*T := by
      rw [paid_constant]
      exact Nat.mul_le_mul_left capacity (truncate_paid_le T _ _)
    have hscore := (score_sum_le zero oracle support off (fun _=>capacity) cap ct pool).trans
      (Nat.add_le_add_left hT _)
    calc
      _ ≤ ∑ p ∈ pairs, (wins p : ℝ≥0∞) := Finset.sum_le_sum fun p _ => hflag p
      _ = (↑(∑ p ∈ pairs, wins p) : ℝ≥0∞) := by simp
      _ ≤ _ := by exact_mod_cast hsum ▸ hscore
  have hu : (∑ p ∈ pairs, μ (event p)) ≤ (↑(pool.card + capacity*T) : ℝ≥0∞) := by
    calc
      _ = ∫⁻ i, ∑ p ∈ pairs, flag p i ∂μ := by
        rw [lintegral_finset_sum' pairs (fun p h =>
          (aemeasurable_indicator_const_iff (1:ℝ≥0∞)).mpr (hm p h))]
        exact Finset.sum_congr rfl fun p h => by
          simp [lintegral_indicator_const₀ (hm p h)]
      _ ≤ _ := (lintegral_mono hpoint).trans_eq (by simp)
  have hue := ENNReal.toReal_mono (ENNReal.natCast_ne_top _) hu
  rw [ENNReal.toReal_sum (fun p _ => (measure_lt_top μ (event p)).ne),
    ENNReal.toReal_natCast] at hue
  have hle := (Finset.sum_le_sum (s := pairs) hl).trans hue
  have hcard : pairs.card = pool.card * 2 := by simp [pairs]
  rw [Finset.sum_const,nsmul_eq_mul,hcard] at hle
  push_cast at hle
  have hnd : (pool.card : ℝ) ≤ 6 * ((capacity*T : ℕ) : ℝ) := by
    push_cast
    linarith
  exact_mod_cast hnd

/-- The two measured random variables belong to the original run. No
structure or measurability on the type of strategies is used. -/
def ExpectedGuarantee {Q R W : Type*} (oracle : W → Bool → Q → R)
    (counted : Q → Bool) (target : W → Bool → Bool) (exponent : ℕ) : Prop :=
  ∀ {Seed : Type u} [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ]
    (budget : ℝ≥0) (trees : Seed → DecisionTree Q R),
    (∀ w b, AEMeasurable (fun i => (paidCount counted (oracle w b) trees i : ℝ≥0∞)) μ) →
    (∀ w b, NullMeasurableSet (goodSeeds (oracle w b) trees (target w b)) μ) →
    (∀ w b, expectedPaid μ counted (oracle w b) trees ≤ (budget : ℝ≥0∞)) →
    (∀ w b, (2:ℝ)/3 ≤ probability μ (goodSeeds (oracle w b) trees (target w b))) →
    (2:ℝ)^exponent / 72 ≤ (budget : ℝ)

/-- The finite promise in the native applications consists of a pair
for every Boolean word. Only the size of the support cylinder differs. -/
theorem words_expected {k exponent : ℕ} (hexp : exponent ≤ k) (zero : R)
    (oracle : (Fin k → Bool) → Bool → Q → R)
    (counted : Q → Bool) (target : (Fin k → Bool) → Bool → Bool)
    (target_eq : ∀ w b, target w b = b)
    (support : Q → Finset (Fin k → Bool))
    (off : ∀ w b q, w ∉ support q → oracle w b q = zero)
    (freeConstant : ∀ w b q, counted q = false → oracle w b q = zero)
    (cap : ∀ q, (support q).card ≤ 2^(k-exponent)) :
    ExpectedGuarantee.{u} oracle counted target exponent := by
  classical
  intro Ω _ μ _ budget trees measurableCost measurableSuccess mean success
  have hu := capacity_at_probability_cutoff μ zero oracle support off counted freeConstant
    (2^(k-exponent)) cap trees Finset.univ budget
    (fun w _ b => measurableCost w b)
    (fun w _ b => by simpa only [target_eq] using measurableSuccess w b)
    (fun w _ b => mean w b)
    (fun w _ b => by simpa only [target_eq] using success w b)
  have hb : 2^k ≤ 6*(2^(k-exponent)*cutoff budget) := by
    simpa only [Finset.card_univ,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] using hu
  have h6 := remove_capacity_factor k exponent (2*cutoff budget) hexp (by
    convert hb using 1
    ring)
  exact exponent_bound budget exponent (by omega)

/-- The complete-only menu has singleton support and uses the full exponent. -/
theorem complete_words_expected {k : ℕ} (zero : R)
    (oracle : (Fin k → Bool) → Bool → Q → R)
    (counted : Q → Bool) (target : (Fin k → Bool) → Bool → Bool)
    (target_eq : ∀ w b, target w b = b)
    (support : Q → Finset (Fin k → Bool))
    (off : ∀ w b q, w ∉ support q → oracle w b q = zero)
    (freeConstant : ∀ w b q, counted q = false → oracle w b q = zero)
    (cap : ∀ q, (support q).card ≤ 1) :
    ExpectedGuarantee.{u} oracle counted target k := by
  apply words_expected (Nat.le_refl k) zero oracle counted target target_eq support off freeConstant
  simpa only [Nat.sub_self,pow_zero] using cap

/-- Equivalently the supremum of the actual paid means has the same bound.
An infinite supremum already satisfies the extended-real inequality. -/
theorem words_expected_sup {k exponent : ℕ} (hexp : exponent ≤ k) (zero : R)
    (oracle : (Fin k → Bool) → Bool → Q → R) (counted : Q → Bool)
    (target : (Fin k → Bool) → Bool → Bool) (target_eq : ∀ w b, target w b = b)
    (support : Q → Finset (Fin k → Bool))
    (off : ∀ w b q, w ∉ support q → oracle w b q = zero)
    (freeConstant : ∀ w b q, counted q = false → oracle w b q = zero)
    (cap : ∀ q, (support q).card ≤ 2^(k-exponent))
    (μ : Measure Seed) [IsProbabilityMeasure μ] (trees : Seed → DecisionTree Q R)
    (measCost : ∀ w b, AEMeasurable (fun i => (paidCount counted (oracle w b) trees i : ℝ≥0∞)) μ)
    (measSuccess : ∀ w b, NullMeasurableSet (goodSeeds (oracle w b) trees (target w b)) μ)
    (success : ∀ w b, (2:ℝ)/3 ≤ probability μ (goodSeeds (oracle w b) trees (target w b))) :
    ENNReal.ofReal ((2:ℝ)^exponent / 72) ≤ ⨆ w, ⨆ b, expectedPaid μ counted (oracle w b) trees := by
  let value := ⨆ w, ⨆ b, expectedPaid μ counted (oracle w b) trees
  change _ ≤ value
  by_cases he : value = ∞
  · rw [he]
    exact le_top
  · apply (ENNReal.ofReal_le_iff_le_toReal he).mpr
    have hmean (w : Fin k → Bool) (b : Bool) :
        expectedPaid μ counted (oracle w b) trees ≤ (value.toNNReal : ℝ≥0∞) := by
      rw [ENNReal.coe_toNNReal he]
      exact (le_iSup (fun b => expectedPaid μ counted (oracle w b) trees) b).trans
        (le_iSup (fun w => ⨆ b, expectedPaid μ counted (oracle w b) trees) w)
    exact words_expected hexp zero oracle counted target target_eq support off freeConstant cap
      μ value.toNNReal trees measCost measSuccess hmean success

#print axioms exponent_bound
#print axioms bad_probability
#print axioms kept_probability
#print axioms capacity_at_probability_cutoff
#print axioms words_expected
#print axioms complete_words_expected
#print axioms words_expected_sup
set_option pp.universes true in
#check @ExpectedGuarantee

end
end J2R119Probability

