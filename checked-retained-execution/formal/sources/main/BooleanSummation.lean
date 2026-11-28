import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

/-!
# Summing Boolean monomials with filtered coefficients

For a squarefree monomial supported on `S`, the sum over all assignments of
the finite index type `ι` equals `2^(card ι - card S)`. Repeated positive
variable powers have the same Boolean values. A coefficient divisible by
`2^j` can offset `j` additional supported variables. The proof evaluates
the cube sum on every monomial and then sums the resulting divisibilities.

In the native-slot application, `ι` consists of unsupported original
column equalities. The assignment and mode expansion proving the support
hypotheses is the separate source argument in P3 and P5.
-/

namespace BooleanSummation

open scoped BigOperators

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]

/-- Send a Boolean variable to zero or one in the coefficient semiring. -/
def bitValue (b : Bool) : R := if b then 1 else 0

/-- The product of the distinct variables in a finite support. -/
def monomial (s : Finset ι) (x : ι → Bool) : R :=
  ∏ i ∈ s, bitValue (R := R) (x i)

/-- Positive powers of one Boolean variable collapse to one occurrence. -/
theorem powers_on_cube (e : ι → ℕ) (x : ι → Bool) :
    (∏ i, bitValue (R := R) (x i) ^ e i) =
      monomial (R := R) (Finset.univ.filter (fun i => e i ≠ 0)) x := by
  classical
  unfold monomial
  rw [← Fintype.prod_ite_mem (Finset.univ.filter (fun i => e i ≠ 0))
    (fun i => bitValue (R := R) (x i))]
  apply Finset.prod_congr rfl
  intro i _
  by_cases he : e i = 0
  · simp [he]
  · cases x i <;> simp [bitValue, he]

/-- Each supported Boolean coordinate contributes one to the variable sum,
and each unsupported coordinate contributes two. -/
theorem sum_monomial (s : Finset ι) :
    (∑ x : ι → Bool, monomial (R := R) s x) =
      (2 : R) ^ (Fintype.card ι - s.card) := by
  classical
  let f : ι → Bool → R := fun i b => if i ∈ s then bitValue b else 1
  calc
    (∑ x : ι → Bool, monomial (R := R) s x) =
        ∑ x : ι → Bool, ∏ i, f i (x i) := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Fintype.prod_ite_mem s (fun i => bitValue (R := R) (x i))).symm
    _ = ∏ i, ∑ b : Bool, f i b := (Fintype.prod_sum f).symm
    _ = ∏ i, (if i ∈ sᶜ then (2 : R) else 1) := by
      apply Finset.prod_congr rfl
      intro i _
      by_cases hi : i ∈ s <;> simp [f, hi, bitValue, Fintype.univ_bool, one_add_one_eq_two]
    _ = (2 : R) ^ (Fintype.card ι - s.card) := by
      rw [Fintype.prod_ite_mem sᶜ (fun _ => (2 : R)), Finset.prod_const, Finset.card_compl]

/-- One weighted monomial. The bound allows powers already supplied by its
coefficient as well as the exact contribution from its absent variables. -/
theorem filtered_monomial (s : Finset ι) (c : R) (k j : ℕ)
    (hs : s.card ≤ k + j) (hc : (2 : R) ^ j ∣ c) :
    (2 : R) ^ (Fintype.card ι - k) ∣
      ∑ x : ι → Bool, c * monomial s x := by
  rw [← Finset.mul_sum, sum_monomial]
  obtain ⟨y, hy⟩ := hc
  have hle : Fintype.card ι - k ≤ j + (Fintype.card ι - s.card) := by omega
  refine (pow_dvd_pow (2 : R) hle).trans ?_
  refine ⟨y, ?_⟩
  rw [hy, pow_add]
  ac_rfl

/-- An arbitrary finite linear combination, including coefficients with
different dyadic weights. No independence between terms is assumed. -/
theorem filtered_cube_sum {τ : Type*} (terms : Finset τ)
    (support : τ → Finset ι) (coeff : τ → R) (weight : τ → ℕ) (k : ℕ)
    (hs : ∀ m ∈ terms, (support m).card ≤ k + weight m)
    (hc : ∀ m ∈ terms, (2 : R) ^ weight m ∣ coeff m) :
    (2 : R) ^ (Fintype.card ι - k) ∣
      ∑ x : ι → Bool, ∑ m ∈ terms, coeff m * monomial (support m) x := by
  rw [Finset.sum_comm]
  exact Finset.dvd_sum fun m hm => filtered_monomial _ _ _ _ (hs m hm) (hc m hm)

/-- Ordinary support degree at most `d` suffices without a coefficient
filtration. This includes the boundary cases d ≥ card ι and an empty cube. -/
theorem bounded_support_cube_sum {τ : Type*} (terms : Finset τ)
    (support : τ → Finset ι) (coeff : τ → R) (d : ℕ)
    (hs : ∀ m ∈ terms, (support m).card ≤ d) :
    (2 : R) ^ (Fintype.card ι - d) ∣
      ∑ x : ι → Bool, ∑ m ∈ terms, coeff m * monomial (support m) x := by
  apply filtered_cube_sum terms support coeff (fun _ => 0) d
  · simpa using hs
  · simp

omit [DecidableEq ι] in
/-- The number of positively powered variables is at most the ordinary
total degree of an exponent vector. -/
theorem support_le_total_degree (e : ι → ℕ) :
    (Finset.univ.filter (fun i => e i ≠ 0)).card ≤ ∑ i, e i := by
  calc
    (Finset.univ.filter (fun i => e i ≠ 0)).card =
        ∑ i, (if e i ≠ 0 then 1 else 0 : ℕ) :=
      Finset.natCast_card_filter (R := ℕ) (fun i => e i ≠ 0) Finset.univ
    _ ≤ ∑ i, e i := by
      apply Finset.sum_le_sum
      intro i _
      split <;> omega

/-- A polynomial written with ordinary, possibly repeated powers. The
termwise total degree bound implies divisibility of the complete cube sum. -/
theorem total_degree_cube_sum {τ : Type*} (terms : Finset τ)
    (e : τ → ι → ℕ) (coeff : τ → R) (d : ℕ)
    (hs : ∀ m ∈ terms, (∑ i, e m i) ≤ d) :
    (2 : R) ^ (Fintype.card ι - d) ∣
      ∑ x : ι → Bool, ∑ m ∈ terms, coeff m * ∏ i, bitValue (R := R) (x i) ^ e m i := by
  simp only [powers_on_cube]
  apply bounded_support_cube_sum
  exact fun m hm => (support_le_total_degree (e m)).trans (hs m hm)

/-- Native coefficient accounting at degree `j`. Each monomial may use up
to `k+j` equality bits and the coefficient has the explicit global factor
`2^(v+j)`. This proves the ordinary z-coefficient bound underlying P5–P7. -/
theorem native_graded_coefficient {τ : Type*} (terms : Finset τ)
    (support : τ → Finset ι) (coeff : τ → R) (v k j : ℕ)
    (hs : ∀ m ∈ terms, (support m).card ≤ k + j) :
    (2 : R) ^ (v + max j (Fintype.card ι - k)) ∣
      (2 : R) ^ (v + j) *
        (∑ x : ι → Bool, ∑ m ∈ terms, coeff m * monomial (support m) x) := by
  obtain ⟨c, hc⟩ := bounded_support_cube_sum terms support coeff (k + j) hs
  refine ⟨c, ?_⟩
  have h : (v + j) + (Fintype.card ι - (k + j)) =
      v + max j (Fintype.card ι - k) := by omega
  rw [hc, ← mul_assoc, ← pow_add, h]

/-- Every evaluation of a finite graded jet vanishes when the output
precision lies below the unsupported-bit bound. The probe is arbitrary. -/
theorem graded_evaluation_zero {τ : Type*} (orders : Finset ℕ) (terms : ℕ → Finset τ)
    (support : ℕ → τ → Finset ι) (coeff : ℕ → τ → R) (v k p : ℕ) (z : R)
    (hchar : (2 : R) ^ p = 0) (hp : p ≤ v + (Fintype.card ι - k))
    (hs : ∀ j ∈ orders, ∀ m ∈ terms j, (support j m).card ≤ k + j) :
    (∑ j ∈ orders, ((2 : R) ^ (v + j) *
      (∑ x : ι → Bool, ∑ m ∈ terms j, coeff j m * monomial (support j m) x)) *
        z ^ (k + j)) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  have hle : p ≤ v + max j (Fintype.card ι - k) :=
    hp.trans (Nat.add_le_add_left (le_max_right _ _) _)
  have hdiv := native_graded_coefficient (terms j) (support j) (coeff j) v k j (hs j hj)
  obtain ⟨w, hw⟩ := (pow_dvd_pow (2 : R) hle).trans hdiv
  rw [hw, hchar, zero_mul, zero_mul]

#print axioms powers_on_cube
#print axioms sum_monomial
#print axioms filtered_monomial
#print axioms filtered_cube_sum
#print axioms bounded_support_cube_sum
#print axioms support_le_total_degree
#print axioms total_degree_cube_sum
#print axioms native_graded_coefficient
#print axioms graded_evaluation_zero

end BooleanSummation
