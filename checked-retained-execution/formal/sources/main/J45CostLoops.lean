import JointContraction
import V9BitCost

/-! Exact loop addresses and a dense-bit tariff for J4–J5. Charges are for
this evaluator, not lower bounds on any other evaluator or an assertion
about machine instructions executed by Lean's kernel. -/
namespace J45Cost
open scoped BigOperators Classical

abbrev Pattern (M : Type*) := M → Bool
abbrev StateBox {D : Type*} (H : D → ℕ) := (d : D) → Fin (H d+1)
abbrev WorkAddress (M : Type*) {D V : Type*} (H : D → ℕ) (U : V → Type*) :=
  Pattern M × (StateBox H × (Σ v, U v))

/-- Every destination, boundary word and local column assignment is one
gather visit. No full original Boolean assignments are in this address set. -/
theorem visit_count {M D V : Type*} [Fintype M] [Fintype D] [Fintype V]
    (H : D → ℕ) (U : V → Type*) [∀ v,Fintype (U v)] :
    Fintype.card (WorkAddress M H U) =
      2^Fintype.card M * (∏ d, (H d+1)) * ∑ v, Fintype.card (U v) := by
  classical
  simp [mul_assoc]

/-- At bounded column degree, the scan is linear in the number of local
vertices and exponential only in that degree, the boundary and the box. -/
theorem visits_degree {M D V : Type*} [Fintype M] [Fintype D] [Fintype V]
    (H : D → ℕ) (Q : V → Type*) [∀ v,Fintype (Q v)] (deg : ℕ)
    (hdeg : ∀ v, Fintype.card (Q v) ≤ deg) :
    Fintype.card (WorkAddress M H (fun v => Q v → Bool)) ≤
      2^Fintype.card M * (∏ d, (H d+1)) * (Fintype.card V * 2^deg) := by
  classical
  rw [visit_count]
  refine Nat.mul_le_mul_left _ ?_
  calc
    (∑ v, Fintype.card (Q v → Bool)) ≤ ∑ _v : V, 2^deg := by
      refine Finset.sum_le_sum fun v _ => ?_
      rw [Fintype.card_fun, Fintype.card_bool]
      exact Nat.pow_le_pow_right (by decide) (hdeg v)
    _ = _ := by simp

abbrev RowTerm (P : A → Type*) := Σ a, (P a → Bool)
abbrev RowMultiply (P : A → Type*) := Σ a, (P a → Bool) × Option (P a)
abbrev GuardTests (M : Type*) (Q : B → Type*) := Σ b, (Q b → Bool) × (Q b × M)

/-- The wired literal product needs d multiplies and its table weight one
more. The schedule includes zero-degree vertices exactly once per word. -/
theorem row_multiply_count {A : Type*} [Fintype A]
    (P : A → Type*) [∀ a,Fintype (P a)] :
    Fintype.card (RowMultiply P) = ∑ a, 2^(Fintype.card (P a)) * (Fintype.card (P a)+1) := by
  classical
  simp

/-- The literal guard from JointContraction.agrees can be checked by the
dense loop over pairs of local logical port and public boundary index. -/
theorem guard_test_count {B M : Type*} [Fintype B] [Fintype M]
    (Q : B → Type*) [∀ b,Fintype (Q b)] :
    Fintype.card (GuardTests M Q) =
      ∑ b, 2^(Fintype.card (Q b)) * (Fintype.card (Q b) * Fintype.card M) := by
  classical
  simp

/-- J4's scan can have one vertex evaluation per boundary pattern,
enumerating original local inputs rather than global assignments. -/
theorem zeroProbe_loop_count {A B M : Type*} [Fintype A] [Fintype B] [Fintype M]
    (P : A → Type*) (Q : B → Type*) [∀ a,Fintype (P a)] [∀ b,Fintype (Q b)] :
    Fintype.card (Pattern M × (RowMultiply P ⊕ GuardTests M Q)) =
    2^Fintype.card M *
      ((∑ a, 2^Fintype.card (P a) * (Fintype.card (P a)+1)) +
        ∑ b, 2^Fintype.card (Q b) * (Fintype.card (Q b)*Fintype.card M)) := by
  classical
  rw [Fintype.card_prod, Fintype.card_sum, row_multiply_count, guard_test_count]
  simp

/-- Double-buffered old/new tables and one across-pattern result table. The
word count for array storage is literal, not a model of the recursion stack. -/
theorem array_words {D : Type*} [Fintype D] (H : D → ℕ) (e : ℕ) :
    Fintype.card ((Fin 3 × StateBox H) × Fin e) = 3*(∏ d, (H d+1))*e := by
  classical
  simp

theorem feature_word_fits {D : Type*} (H bits : D → ℕ)
    (h : ∀ d,H d < 2^(bits d)) (s : StateBox H) (d : D) :
    (s d).val < 2^(bits d) := by
  have hs := (s d).isLt
  exact (Nat.lt_succ_iff.mp hs).trans_lt (h d)

/-- Each gather address uses at most one multiplication of e residue words,
and one accumulating addition of e residue words. addressTape explicitly
pays for the guard, computing a shifted tuple, value lookup and iteration. -/
def gatherTariff (e p addressTape : ℕ) : ℕ :=
  V9BitCost.ringMulEnvelope e p + e*(p+1) + addressTape

theorem gatherTariff_le (e p addressTape : ℕ) :
    gatherTariff e p addressTape ≤ 21*(e+1)^2*(p+1)^2 + addressTape := by
  have hm := V9BitCost.ringMulEnvelope_le e p
  have he : e ≤ (e+1)^2 := by nlinarith
  have hp : p+1 ≤ (p+1)^2 := by nlinarith
  have ha := Nat.mul_le_mul he hp
  unfold gatherTariff
  nlinarith

/-- The all-pattern DP cost in the bit-serial tariff, excluding table
initialization and the separately counted row reduction. -/
theorem charged_gather {M D V : Type*} [Fintype M] [Fintype D] [Fintype V]
    (H : D → ℕ) (U : V → Type*) [∀ v,Fintype (U v)]
    (e p addressTape : ℕ) :
    Fintype.card (WorkAddress M H U) * gatherTariff e p addressTape ≤
      2^Fintype.card M * (∏ d, (H d + 1)) * (∑ v, Fintype.card (U v)) *
        (21*(e+1)^2*(p+1)^2+addressTape) := by
  rw [visit_count]
  exact Nat.mul_le_mul_left _ (gatherTariff_le e p addressTape)

theorem old_coefficient_fits (p : ℕ) (x : ZMod (2^p)) : x.val < 2^p :=
  V9BitCost.canonical_width p x

section Powers

variable {R : Type*} [Monoid R]

/-- Read the actual supplied binary tape from most significant digit to
least significant, squaring then optionally multiplying by the base. -/
def digitExponent : List Bool → ℕ → ℕ
  | [], acc => acc
  | bit::bits, acc => digitExponent bits (acc+acc+(if bit then 1 else 0))

def digitPower (x : R) : List Bool → R → R
  | [], acc => acc
  | bit::bits, acc => digitPower x bits (acc*acc*(if bit then x else 1))

theorem digitPower_exact (x : R) (bits : List Bool) (n : ℕ) :
    digitPower x bits (x^n) = x^(digitExponent bits n) := by
  induction bits generalizing n with
  | nil => rfl
  | cons b bs ih =>
    have h : x^n*x^n*(if b then x else 1) = x^(n+n+(if b then 1 else 0)) := by
      rw [← pow_add,pow_add x (n+n)]
      cases b <;> simp
    rw [digitPower,digitExponent,h,ih]

/-- The exact multiplication tariff for the supplied tape, charging one
square per digit plus one multiply exactly when the digit is one. -/
def digitMultiplications : List Bool → ℕ
  | [] => 0
  | bit::bits => (if bit then 2 else 1) + digitMultiplications bits

theorem digitMultiplications_le (bits : List Bool) :
    digitMultiplications bits ≤ 2*bits.length := by
  induction bits with
  | nil => simp [digitMultiplications]
  | cons b bs ih => cases b <;> simp [digitMultiplications] <;> omega

end Powers

#print axioms visit_count
#print axioms visits_degree
#print axioms row_multiply_count
#print axioms guard_test_count
#print axioms zeroProbe_loop_count
#print axioms array_words
#print axioms feature_word_fits
#print axioms gatherTariff_le
#print axioms charged_gather
#print axioms old_coefficient_fits
#print axioms digitPower_exact
#print axioms digitMultiplications_le

end J45Cost