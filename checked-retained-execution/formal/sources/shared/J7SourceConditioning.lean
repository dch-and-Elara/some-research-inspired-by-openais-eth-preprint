import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic

/-!
# Exact local conditioning and covariance for J7 source labels

Conditional draws here are finite rational product measures. On a partially
fixed block, use a point mass; on a free block, use its original normalized
law. The same identities apply to both. The given completion is used only
to express a function already known to depend on its stated support.
-/

open scoped BigOperators Classical

namespace J7SourceConditioning

noncomputable section

section FiniteLaw

variable {Ω : Type*} [Fintype Ω]

def expect (weight f : Ω → ℚ) : ℚ := ∑ ω, weight ω * f ω

theorem expect_const (weight : Ω → ℚ) (h : ∑ ω, weight ω = 1) (c : ℚ) :
    expect weight (fun _ => c) = c := by
  simp only [expect, ← Finset.sum_mul, h, one_mul]

theorem expect_sum {ι : Type*} (s : Finset ι) (weight : Ω → ℚ) (f : ι → Ω → ℚ) :
    expect weight (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, expect weight (f i) := by
  unfold expect
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem expect_nonneg (weight f : Ω → ℚ) (hw : ∀ ω, 0 ≤ weight ω)
    (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ expect weight f :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (hw ω) (hf ω)

theorem expect_le (weight f g : Ω → ℚ) (hw : ∀ ω, 0 ≤ weight ω)
    (h : ∀ ω, f ω ≤ g ω) : expect weight f ≤ expect weight g :=
  Finset.sum_le_sum fun ω _ => mul_le_mul_of_nonneg_left (h ω) (hw ω)

end FiniteLaw

section ProductLaw

variable {I : Type*} [Fintype I] {A : I → Type*} [∀ i, Fintype (A i)]

def productWeight (w : ∀ i, A i → ℚ) (z : ∀ i, A i) : ℚ := ∏ i, w i (z i)

def average (w : ∀ i, A i → ℚ) (f : (∀ i, A i) → ℚ) : ℚ :=
  expect (productWeight w) f

theorem productWeight_normalized (w : ∀ i, A i → ℚ) (h : ∀ i, ∑ a, w i a = 1) :
    (∑ z : (∀ i, A i), productWeight w z) = 1 := by
  unfold productWeight
  rw [← Fintype.prod_sum]
  simp [h]

omit [∀ i, Fintype (A i)] in
theorem productWeight_nonneg (w : ∀ i, A i → ℚ) (h : ∀ i a, 0 ≤ w i a)
    (z : ∀ i, A i) : 0 ≤ productWeight w z :=
  Finset.prod_nonneg fun i _ => h i (z i)

abbrev Part (A : I → Type*) (p : I → Prop) := (i : Subtype p) → A i

def restrict (p : I → Prop) (z : ∀ i, A i) : Part A p := fun i => z i

def fill (p : I → Prop) (reference : ∀ i, A i) (z : Part A p) : ∀ i, A i :=
  fun i => if h : p i then z ⟨i, h⟩ else reference i

/-- A numerical load component only uses the blocks in p. -/
def depends (p : I → Prop) (f : (∀ i, A i) → ℚ) : Prop :=
  ∀ x y : (∀ i, A i), (∀ i, p i → x i = y i) → f x = f y

theorem split_expectation (w : ∀ i, A i → ℚ) (p : I → Prop)
    (f : Part A p → ℚ) (g : Part A (fun i => ¬ p i) → ℚ) :
    average w (fun z => f (restrict p z) * g (restrict (fun i => ¬p i) z)) =
      average (fun i : Subtype p => w i) f * average (fun i : {i // ¬p i} => w i) g := by
  let e := Equiv.piEquivPiSubtypeProd p A
  have hprod (z : ∀ i, A i) :
      productWeight w z =
        productWeight (fun i : Subtype p => w i) (restrict p z) *
          productWeight (fun i : {i // ¬p i} => w i) (restrict (fun i => ¬p i) z) :=
    (Fintype.prod_subtype_mul_prod_subtype p fun i => w i (z i)).symm
  calc
    _ =
        ∑ a : Part A p × Part A (fun i => ¬p i),
          (productWeight (fun i : Subtype p => w i) a.1 * f a.1) *
          (productWeight (fun i : {i // ¬p i} => w i) a.2 * g a.2) := by
      unfold average expect
      refine Fintype.sum_equiv e _ _ fun z => ?_
      change productWeight w z * (f (restrict p z) * g (restrict (fun i => ¬p i) z)) =
        (productWeight (fun i : Subtype p => w i) (restrict p z) * f (restrict p z)) *
          (productWeight (fun i : {i // ¬p i} => w i) (restrict (fun i => ¬p i) z) *
            g (restrict (fun i => ¬p i) z))
      rw [hprod]
      ac_rfl
    _ = _ := by
      unfold average expect
      rw [Fintype.sum_prod_type, Finset.sum_mul]
      refine Finset.sum_congr (by ext a; simp) fun a _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr (by ext b; simp) fun _ _ => rfl

/-- Delete all blocks outside the support from the exact conditional sum.
Applying this to a two-wire cell predicate uses only the union of their
source supports (at most four blocks for the physical layout). -/
theorem expectation_only_support (w : ∀ i, A i → ℚ) (h : ∀ i, ∑ a, w i a = 1)
    (p : I → Prop) (reference : ∀ i, A i) (f : (∀ i, A i) → ℚ)
    (hf : depends p f) :
    average w f = average (fun i : Subtype p => w i) (fun u => f (fill p reference u)) := by
  let fp := fun u => f (fill p reference u)
  have hdep (z : ∀ i, A i) : f z = fp (restrict p z) := by
    apply hf
    intro i hi
    simp [fill, restrict, hi]
  have hs := split_expectation w p fp (fun _ => 1)
  simp only [mul_one] at hs
  have h1 : average (fun i : {i // ¬p i} => w i) (fun _ => 1) = 1 := by
    unfold average expect
    simp only [mul_one]
    convert (productWeight_normalized (fun i : {i // ¬p i} => w i) fun i => h i) using 1
  rw [h1, mul_one] at hs
  rw [← hs]
  unfold average
  exact congrArg (expect (productWeight w)) (funext hdep)

/-- Source wires reading disjoint primitive blocks have exactly independent
indicators. Neither edge endpoints nor the two gadgets sharing a block
are treated as independent. -/
theorem expectation_disjoint_supports (w : ∀ i, A i → ℚ) (h : ∀ i, ∑ a, w i a = 1)
    (p q : I → Prop) (disj : ∀ i, p i → q i → False) (reference : ∀ i, A i)
    (f g : (∀ i, A i) → ℚ) (hf : depends p f) (hg : depends q g) :
    average w (fun z => f z * g z) = average w f * average w g := by
  have hg' : depends (fun i => ¬p i) g := by
    intro x y hxy
    apply hg
    intro i hi
    exact hxy i (fun hp => disj i hp hi)
  let fp := fun u => f (fill p reference u)
  let gp := fun u => g (fill (fun i => ¬p i) reference u)
  have hf' (z : ∀ i, A i) : f z = fp (restrict p z) := by
    apply hf
    intro i hi
    simp [fill, restrict, hi]
  have hg'' (z : ∀ i, A i) : g z = gp (restrict (fun i => ¬p i) z) := by
    apply hg'
    intro i hi
    simp [fill, restrict, hi]
  calc
    _ = average w (fun z => fp (restrict p z) * gp (restrict (fun i => ¬p i) z)) := by
      unfold average
      exact congrArg (expect (productWeight w)) (funext fun z => congrArg₂ (· * ·) (hf' z) (hg'' z))
    _ = _ := by
      rw [split_expectation, expectation_only_support w h p reference f hf,
        expectation_only_support w h (fun i => ¬p i) reference g hg']
      dsimp only [fp, gp]
      congr 1
      congr 1
      exact Subsingleton.elim _ _

end ProductLaw

section CovarianceTrace

variable {Ω E C : Type*} [Fintype Ω] [Fintype C]

def indicator (x y : C) : ℚ := if x = y then 1 else 0

def meanCell (weight : Ω → ℚ) (label : E → Ω → C) (e : E) (c : C) : ℚ :=
  expect weight (fun z => indicator (label e z) c)

def centered (weight : Ω → ℚ) (label : E → Ω → C) (e : E) (c : C) (z : Ω) : ℚ :=
  indicator (label e z) c - meanCell weight label e c

def traceCov (weight : Ω → ℚ) (label : E → Ω → C) (e f : E) : ℚ :=
  ∑ c, expect weight (fun z => centered weight label e c z * centered weight label f c z)

def varianceScore (s : Finset E) (weight : Ω → ℚ) (label : E → Ω → C) (z : Ω) : ℚ :=
  ∑ c, (∑ e ∈ s, centered weight label e c z)^2

theorem varianceScore_expansion (s : Finset E) (weight : Ω → ℚ) (label : E → Ω → C) :
    expect weight (varianceScore s weight label) = ∑ e ∈ s, ∑ f ∈ s, traceCov weight label e f := by
  unfold varianceScore traceCov
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum, expect_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm

private theorem center_expand (weight f g : Ω → ℚ) (h : ∑ z, weight z = 1) :
    expect weight (fun z => (f z - expect weight f) * (g z - expect weight g)) =
      expect weight (fun z => f z * g z) - expect weight f * expect weight g := by
  have h₁ : expect weight (fun z => f z * expect weight g) = expect weight f * expect weight g := by
    simp only [expect, ← mul_assoc, Finset.sum_mul]
  have h₂ : expect weight (fun z => expect weight f * g z) = expect weight f * expect weight g := by
    unfold expect
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ac_rfl
  have hs (a b : Ω → ℚ) :
      expect weight (fun z => a z + b z) = expect weight a + expect weight b := by
    simp [expect, mul_add, Finset.sum_add_distrib]
  have hd (a b : Ω → ℚ) :
      expect weight (fun z => a z - b z) = expect weight a - expect weight b := by
    simp [expect, mul_sub, Finset.sum_sub_distrib]
  simp_rw [sub_mul, mul_sub]
  rw [hd, hd, hd, h₁, h₂, expect_const _ h]
  ring

omit [Fintype C] in
theorem centered_product (weight : Ω → ℚ) (label : E → Ω → C)
    (norm : ∑ z, weight z = 1) (e f : E) (c : C) :
    expect weight (fun z => centered weight label e c z * centered weight label f c z) =
      expect weight (fun z => indicator (label e z) c * indicator (label f z) c) -
        meanCell weight label e c * meanCell weight label f c :=
  center_expand weight (fun z => indicator (label e z) c) (fun z => indicator (label f z) c) norm

/-- The covariance trace of one ordered pair is at most one, even if its
individual cell labels have different nonuniform marginals. -/
theorem traceCov_le_one (weight : Ω → ℚ) (label : E → Ω → C)
    (nonneg : ∀ z, 0 ≤ weight z) (norm : ∑ z, weight z = 1) (e f : E) :
    traceCov weight label e f ≤ 1 := by
  have hμ (d : E) (c : C) : 0 ≤ meanCell weight label d c :=
    expect_nonneg _ _ nonneg (fun z => by unfold indicator; split <;> norm_num)
  have hm : (∑ c, expect weight (fun z => indicator (label e z) c * indicator (label f z) c)) ≤ 1 := by
    rw [← expect_sum]
    calc
      _ ≤ expect weight (fun _ => 1) := expect_le _ _ _ nonneg fun z => by
        by_cases hz : label e z = label f z
        · simp [indicator, hz]
        · have he : (∑ c, indicator (label e z) c * indicator (label f z) c) = 0 := by
            refine Finset.sum_eq_zero fun c _ => ?_
            by_cases hec : label e z = c
            · subst c
              simp [indicator, Ne.symm hz]
            · simp [indicator, hec]
          rw [he]
          norm_num
      _ = 1 := expect_const _ norm _
  unfold traceCov
  simp_rw [centered_product weight label norm, Finset.sum_sub_distrib]
  apply (sub_le_self _ (Finset.sum_nonneg fun c _ => mul_nonneg (hμ e c) (hμ f c))).trans hm

/-- A pair whose cell indicators have the product joint law gives zero
trace. The product law follows from disjoint source supports above. -/
theorem traceCov_zero (weight : Ω → ℚ) (label : E → Ω → C)
    (norm : ∑ z, weight z = 1) (e f : E)
    (independent : ∀ c,
      expect weight (fun z => indicator (label e z) c * indicator (label f z) c) =
        meanCell weight label e c * meanCell weight label f c) :
    traceCov weight label e f = 0 := by
  unfold traceCov
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [centered_product weight label norm, independent c, sub_self]

/-- Finite score expectation is at most the number of ordered pairs that
can share primitive data. The same theorem applies to the pin sublist. -/
theorem expected_score_le_dependent (s : Finset E) (weight : Ω → ℚ)
    (label : E → Ω → C) (neighbor : E → Finset E)
    (nonneg : ∀ z, 0 ≤ weight z) (norm : ∑ z, weight z = 1)
    (independent : ∀ e ∈ s, ∀ f ∈ s, f ∉ neighbor e → ∀ c,
      expect weight (fun z => indicator (label e z) c * indicator (label f z) c) =
        meanCell weight label e c * meanCell weight label f c) :
    expect weight (varianceScore s weight label) ≤ ∑ e ∈ s, ((neighbor e).card : ℚ) := by
  rw [varianceScore_expansion]
  refine Finset.sum_le_sum fun e he => ?_
  calc
    _ ≤ ∑ f ∈ s, if f ∈ neighbor e then (1 : ℚ) else 0 := by
      refine Finset.sum_le_sum fun f hf => ?_
      by_cases hd : f ∈ neighbor e
      · simpa only [if_pos hd] using traceCov_le_one weight label nonneg norm e f
      · simp only [if_neg hd, traceCov_zero weight label norm e f (independent e he f hf hd), le_refl]
    _ = ((s.filter fun f => f ∈ neighbor e).card : ℚ) := by
      rw [← Finset.sum_filter]; simp
    _ ≤ _ := by
      exact_mod_cast Finset.card_le_card (fun f hf => (Finset.mem_filter.mp hf).2)

end CovarianceTrace

#print axioms productWeight_normalized
#print axioms split_expectation
#print axioms expectation_only_support
#print axioms expectation_disjoint_supports
#print axioms varianceScore_expansion
#print axioms traceCov_le_one
#print axioms traceCov_zero
#print axioms expected_score_le_dependent

end
end J7SourceConditioning
