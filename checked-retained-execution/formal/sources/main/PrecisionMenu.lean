import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Finite.Range
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
# Finite shared coefficient encoding

This module formalizes the finite encoding step in P3–P6 of the native
precision frontier. The source's packet expansions supply the divisibility
premises; they are not reconstructed here. A joint message contains only
base two digits, even when the probes range over an extension ring.
-/

open scoped BigOperators

namespace PrecisionMenu

/-- The number of raw digits in a triangular coefficient staircase. -/
def triangular : ℕ → ℕ
  | 0 => 0
  | n + 1 => triangular n + (n + 1)

/-- Additional coefficient divisibility is encoded by the gap g; the
coefficient at index j needs only n − max(j,g) digits. -/
def width (n g j : ℕ) : ℕ := n - max j g

theorem two_mul_triangular (n : ℕ) : 2 * triangular n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 2 * (triangular n + (n+1)) = (n+1) * (n+1+1)
    rw [Nat.mul_add, ih]
    ring

theorem triangular_eq (n : ℕ) : triangular n = n * (n + 1) / 2 := by
  have h := two_mul_triangular n
  omega

theorem triangular_mono : Monotone triangular := by
  apply monotone_nat_of_le_succ
  intro n
  dsimp [triangular]
  omega

theorem sum_staircase (n : ℕ) :
    (∑ j ∈ Finset.range n, (n - j)) = triangular n := by
  induction n with
  | zero => simp [triangular]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have h (j : ℕ) (hj : j ∈ Finset.range n) : n + 1 - j = n - j + 1 := by
      simp only [Finset.mem_range] at hj
      omega
    rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, ih]
    simp [triangular]
    omega

theorem sum_staircase_cutoff {m n : ℕ} (hmn : m ≤ n) :
    (∑ j ∈ Finset.range n, (m - j)) = triangular m := by
  rw [← sum_staircase m]
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hmn)
  intro j _ hj
  simp only [Finset.mem_range, not_lt] at hj
  exact Nat.sub_eq_zero_of_le hj

/-- P6, exact even when the available precision is at or below the extra
coefficient valuation. Natural subtraction implements positive part. -/
theorem sum_width (n g : ℕ) :
    (∑ j ∈ Finset.range n, width n g j) = triangular n - triangular g := by
  by_cases hg : g ≤ n
  · have hpoint (j : ℕ) (hj : j ∈ Finset.range n) :
        width n g j + (g - j) = n - j := by
      simp only [Finset.mem_range] at hj
      unfold width
      omega
    have hs := Finset.sum_congr rfl hpoint
    rw [Finset.sum_add_distrib, sum_staircase_cutoff hg, sum_staircase] at hs
    omega
  · have hgn : n ≤ g := by omega
    have hpoint (j : ℕ) (_hj : j ∈ Finset.range n) : width n g j = 0 := by
      unfold width
      exact Nat.sub_eq_zero_of_le (hgn.trans (le_max_right j g))
    rw [Finset.sum_congr rfl hpoint, Finset.sum_const_zero]
    exact (Nat.sub_eq_zero_of_le (triangular_mono hgn)).symm

/-- For p output bits, v extracted powers of two, and the remaining
valuation gap g = (K − k)₊, these are all the digits the slot must supply. -/
def SlotDigits (p v g : ℕ) : Type :=
  (j : Fin (p-v)) → Fin (2 ^ width (p-v) g j)

instance (p v g : ℕ) : Fintype (SlotDigits p v g) :=
  inferInstanceAs (Fintype ((j : Fin (p-v)) → Fin (2 ^ width (p-v) g j)))

/-- P6 counts an explicit finite encoding alphabet, not an acquisition time. -/
theorem card_slotDigits (p v g : ℕ) :
    Fintype.card (SlotDigits p v g) =
      2 ^ (triangular (p-v) - triangular g) := by
  change Fintype.card ((j : Fin (p-v)) → Fin (2 ^ width (p-v) g j)) = _
  rw [Fintype.card_pi]
  simp only [Fintype.card_fin, Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range, sum_width]

/-- Any finite menu of addresses with independently allocated digit budgets. -/
def JointDigits {ι : Type*} (p v g : ι → ℕ) : Type _ :=
  (i : ι) → SlotDigits (p i) (v i) (g i)

instance {ι : Type*} [Fintype ι] [DecidableEq ι] (p v g : ι → ℕ) : Fintype (JointDigits p v g) :=
  inferInstanceAs (Fintype ((i : ι) → SlotDigits (p i) (v i) (g i)))

theorem card_jointDigits {ι : Type*} [Fintype ι] [DecidableEq ι] (p v g : ι → ℕ) :
    Fintype.card (JointDigits p v g) =
      2 ^ (∑ i, (triangular (p i-v i) - triangular (g i))) := by
  change Fintype.card ((i : ι) → SlotDigits (p i) (v i) (g i)) = _
  rw [Fintype.card_pi]
  simp only [card_slotDigits, Finset.prod_pow_eq_pow_sum]

section Generating

open Polynomial

/-- The degree less than p geometric series, without introducing an
infinite-series evaluation at a non-nilpotent probe. -/
noncomputable def geometric (p : ℕ) : Polynomial ℕ :=
  ∑ j ∈ Finset.range p, (X : Polynomial ℕ)^j

theorem geometric_coeff {p n : ℕ} (hn : n < p) : (geometric p).coeff n = 1 := by
  rw [geometric, Polynomial.finset_sum_coeff,
    Finset.sum_eq_single_of_mem n (Finset.mem_range.mpr hn)]
  · simp
  · intro j _ hj
    exact (coeff_X_pow j n).trans (if_neg hj.symm)

theorem mul_geometric_coeff (f : Polynomial ℕ) {p n : ℕ} (hn : n < p) :
    (f * geometric p).coeff n = ∑ j ∈ Finset.range (n+1), f.coeff (n-j) := by
  rw [geometric, Finset.mul_sum, Polynomial.finset_sum_coeff]
  simp only [coeff_mul_X_pow']
  symm
  calc
    _ = ∑ j ∈ Finset.range (n+1), if j ≤ n then f.coeff (n-j) else 0 := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [if_pos (by have h := Finset.mem_range.mp hj; omega : j ≤ n)]
    _ = _ := by
      apply Finset.sum_subset (Finset.range_subset_range.mpr (by omega))
      intro j _ hj
      rw [if_neg (by simp only [Finset.mem_range] at hj; omega)]

theorem geometric_sq_coeff {p n : ℕ} (hn : n < p) :
    ((geometric p)^2).coeff n = n+1 := by
  rw [pow_two, mul_geometric_coeff _ hn]
  have hs (j : ℕ) (_ : j ∈ Finset.range (n+1)) :
      (geometric p).coeff (n-j) = 1 := geometric_coeff (by omega)
  rw [Finset.sum_congr rfl hs]
  simp

/-- The third power of the geometric series contributes exactly the
triangular coefficient used in P4. -/
theorem geometric_cube_coeff {p n : ℕ} (hn : n < p) :
    ((geometric p)^3).coeff n = triangular (n+1) := by
  rw [show (3:ℕ)=2+1 by rfl, pow_succ, mul_geometric_coeff _ hn]
  have hs (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      ((geometric p)^2).coeff (n-j) = n+1-j := by
    rw [geometric_sq_coeff (by omega : n-j < p)]
    simp only [Finset.mem_range] at hj
    omega
  rw [Finset.sum_congr rfl hs, sum_staircase]

/-- The degree less than p portion of the series with coefficients T(j+1),
i.e. the coefficient series of the factor (1-X)^(-3) in P4. -/
noncomputable def trianglePolynomial (p : ℕ) : Polynomial ℕ :=
  ∑ j ∈ Finset.range p, monomial j (triangular (j+1))

/-- The finite polynomial version of the product in P4. For positive mode
costs the finite geometric sums have the same relevant coefficients as
their infinite counterparts, including when no mode can affect the slot. -/
noncomputable def menuPolynomial {ι : Type*} [Fintype ι] (p : ℕ) (cost : ι → ℕ) :
    Polynomial ℕ :=
  trianglePolynomial p *
    ∏ i, ∑ e : Fin p, (X : Polynomial ℕ) ^ (cost i * (e : ℕ))

theorem trianglePolynomial_coeff {p n : ℕ} (hn : n < p) :
    (trianglePolynomial p).coeff n = triangular (n+1) := by
  rw [trianglePolynomial, Polynomial.finset_sum_coeff,
    Finset.sum_eq_single_of_mem n (Finset.mem_range.mpr hn)]
  · exact coeff_monomial_same n _
  · intro j _ hj
    exact coeff_monomial_of_ne _ hj.symm

theorem trianglePolynomial_mul_X_coeff (p v : ℕ) :
    (trianglePolynomial p * (X : Polynomial ℕ)^v).coeff (p-1) =
      triangular (p-v) := by
  by_cases hp : p = 0
  · simp [hp, trianglePolynomial, triangular]
  rw [trianglePolynomial, Finset.sum_mul, Polynomial.finset_sum_coeff]
  simp only [X_pow_eq_monomial, monomial_mul_monomial, Nat.mul_one, coeff_monomial]
  by_cases hv : v ≤ p-1
  · have hj : p-1-v ∈ Finset.range p := by
      simp only [Finset.mem_range]
      omega
    rw [Finset.sum_eq_single_of_mem _ hj]
    · rw [if_pos (by omega : p-1-v+v = p-1)]
      congr 1
      omega
    · intro j _ hne
      exact if_neg (by omega)
  · have hzero : p-v = 0 := by omega
    rw [hzero, triangular]
    apply Finset.sum_eq_zero
    intro j _
    exact if_neg (by omega)

/-- The finite generating coefficient equals the sum over every exponent
tuple of its unrefined slot budget. This is the exact combinatorial identity
underlying P4. Each mode occurs once in the product, so repeated costs give
the corresponding geometric factor raised to its multiplicity. -/
theorem threshold_coefficient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) (cost : ι → ℕ) :
    (menuPolynomial p cost).coeff (p-1) =
      ∑ e : ι → Fin p, triangular (p - ∑ i, cost i * (e i : ℕ)) := by
  rw [menuPolynomial, Fintype.prod_sum, Finset.mul_sum, Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.prod_pow_eq_pow_sum, trianglePolynomial_mul_X_coeff]

/-- Directly replacing the triangular polynomial by the third geometric
power gives the same P4 coefficient. The geometric factors may be cut off
at the working precision; only nonnegative exponents are involved. -/
theorem threshold_geometric_coefficient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) (hp : 0 < p) (cost : ι → ℕ) :
    (((geometric p)^3) *
       ∏ i, ∑ e : Fin p, (X : Polynomial ℕ) ^ (cost i * (e : ℕ))).coeff (p-1) =
      ∑ e : ι → Fin p, triangular (p - ∑ i, cost i * (e i : ℕ)) := by
  rw [← threshold_coefficient p cost, menuPolynomial]
  let q := ∏ i, ∑ e : Fin p, (X : Polynomial ℕ) ^ (cost i * (e : ℕ))
  change (((geometric p)^3) * q).coeff (p-1) = (trianglePolynomial p * q).coeff (p-1)
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hs := Finset.mem_antidiagonal.mp hj
  have hlt : j.1 < p := by omega
  rw [geometric_cube_coeff hlt, trianglePolynomial_coeff hlt]

/-- The actual message alphabet for all mode tuples, with no extra
divisibility gap, has exactly the P4 power-of-two cardinality. The range of
any successful observation/decode is bounded by this cardinality. -/
theorem weighted_jointDigits_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ℕ) (hp : 0 < p) (cost : ι → ℕ) :
    Fintype.card (JointDigits (fun _ : ι → Fin p => p)
      (fun e => ∑ i, cost i * (e i : ℕ)) (fun _ => 0)) =
      2 ^ ((((geometric p)^3) *
        ∏ i, ∑ e : Fin p, (X : Polynomial ℕ) ^ (cost i * (e : ℕ))).coeff (p-1)) := by
  classical
  rw [card_jointDigits, threshold_geometric_coefficient p hp cost]
  simp [triangular]

/-- For positive weights our finite exponent type loses no tuple whose
coefficient can influence the requested precision. -/
theorem exponent_lt_precision_of_weight {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (cost e : ι → ℕ) (hc : ∀ i, 1 ≤ cost i)
    (hw : (∑ i, cost i * e i) < p) (i : ι) :
    e i < p := by
  calc
    e i = 1*e i := (Nat.one_mul _).symm
    _ ≤ cost i * e i := Nat.mul_le_mul_right _ (hc i)
    _ ≤ ∑ j, cost j * e j := Finset.single_le_sum (f := fun j => cost j * e j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ < p := hw

end Generating

section BaseDigits

/-- The Euclidean remainder of an integer, as a member of the base digit alphabet. -/
def integerDigit (w : ℕ) (a : ℤ) : Fin (2^w) :=
  ⟨(a % (2:ℤ)^w).toNat, by
    have h0 : 0 < (2:ℤ)^w := by positivity
    have hn := Int.emod_nonneg a (ne_of_gt h0)
    have hl := Int.emod_lt_of_pos a h0
    exact_mod_cast (show (((a % (2:ℤ)^w).toNat : ℕ) : ℤ) < (2:ℤ)^w by
      simpa only [Int.toNat_of_nonneg hn] using hl)⟩

theorem integerDigit_spec (w : ℕ) (a : ℤ) :
    a = ((integerDigit w a : ℕ) : ℤ) + (2:ℤ)^w * (a / (2:ℤ)^w) := by
  have h0 : 0 < (2:ℤ)^w := by positivity
  simpa only [integerDigit, Int.toNat_of_nonneg (Int.emod_nonneg a (ne_of_gt h0))]
    using (Int.emod_add_mul_ediv a ((2:ℤ)^w)).symm

/-- Geometric inverse for an odd integer, computed solely in the base ring. -/
def oddInverse (b : ℤ) : ℕ → ℤ
  | 0 => 0
  | n+1 => 1 + (1-b) * oddInverse b n

theorem oddInverse_spec (s : ℤ) (n : ℕ) :
    oddInverse (2*s+1) n * (2*s+1) = 1 - (2:ℤ)^n * (-s)^n := by
  induction n with
  | zero => simp [oddInverse]
  | succ n ih =>
    calc
      _ = (2*s+1) + (1-(2*s+1)) * (oddInverse (2*s+1) n * (2*s+1)) := by
        rw [oddInverse]
        ring
      _ = _ := by rw [ih, pow_succ, pow_succ]; ring

/-- The selected digit depends on the base numerator and odd denominator
alone, not on the probe or extension. -/
def oddDigit (w : ℕ) (a b : ℤ) : Fin (2^w) :=
  integerDigit w (oddInverse b w * a)

theorem oddDigit_spec {R : Type*} [CommRing R] (w : ℕ) (a b : ℤ)
    (hb : Odd b) (x : R) (hx : (b:R) * x = (a:R)) :
    ∃ q : R, x = ((oddDigit w a b : ℕ):R) + (2:R)^w * q := by
  obtain ⟨s, rfl⟩ := hb
  let b := 2*s+1
  let u := oddInverse b w
  let q₀ := u * a / (2:ℤ)^w
  have hu : (u:R) * (b:R) = 1 - (2:R)^w * (((-s)^w:ℤ):R) := by
    have h := congrArg (fun t : ℤ => (t:R)) (oddInverse_spec s w)
    dsimp only [u, b]
    push_cast at h ⊢
    exact h
  have hd : (u:R) * (a:R) = ((oddDigit w a b : ℕ):R) + (2:R)^w * (q₀:R) := by
    have h := congrArg (fun t : ℤ => (t:R)) (integerDigit_spec w (u*a))
    push_cast at h
    exact h
  refine ⟨(q₀:R) + (((-s)^w:ℤ):R) * x, ?_⟩
  calc
    x = (((u:R) * (b:R)) * x) + (2:R)^w * ((((-s)^w:ℤ):R) * x) := by
      rw [hu]
      ring
    _ = (u:R) * (a:R) + (2:R)^w * ((((-s)^w:ℤ):R) * x) := by
      rw [mul_assoc (u:R), show (b:R)*x = (a:R) from hx]
    _ = _ := by rw [hd]; ring

end BaseDigits

section Decode

variable {R : Type*} [CommRing R]

/-- The valuation-zero coefficient may be arbitrary in the probe ring. The
lower valuation bound of P5 is pulled out of each coefficient first. -/
def evalSlot (p v k : ℕ) (c : Fin (p-v) → R) (z : R) : R :=
  (2 : R)^v * z^k * ∑ j, c j * ((2 : R)*z)^ (j : ℕ)

/-- Decode from a base-ring message, using the same message at all probes. -/
def evalDigits (p v k g : ℕ) (d : SlotDigits p v g) (z : R) : R :=
  evalSlot p v k (fun j => (2 : R)^(g - (j : ℕ)) * ((d j : ℕ) : R)) z

/-- If two to the p is zero, any higher power of two vanishes in the probe ring. -/
theorem pow_two_zero_of_le {p a : ℕ} (hp : (2 : R)^p = 0) (ha : p ≤ a) :
    (2 : R)^a = 0 := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ha
  simp [pow_add, hp]

/-- All omitted Taylor coefficients are immaterial, even at nonunit probes. -/
theorem omitted_term_zero {p v k j : ℕ} (hp : (2 : R)^p = 0)
    (hj : p-v ≤ j) (c z : R) :
    (2 : R)^v * z^k * (c * ((2 : R)*z)^j) = 0 := by
  rw [mul_pow]
  calc
    _ = (2 : R)^(v+j) * (z^(k+j) * c) := by rw [pow_add, pow_add]; ring
    _ = 0 := by rw [pow_two_zero_of_le hp (by omega : p ≤ v+j), zero_mul]

/-- A finite Taylor approximation can be cut off exactly at p-v, with
no assumption on the number or values of the omitted coefficients. -/
theorem truncateFiniteSeries {p v k m : ℕ} (hp : (2 : R)^p = 0)
    (hm : p-v ≤ m) (c : ℕ → R) (z : R) :
    (2 : R)^v * z^k * (∑ j ∈ Finset.range m, c j * ((2 : R)*z)^j) =
      evalSlot p v k (fun j => c j) z := by
  simp only [evalSlot, Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => (2 : R)^v * z^k * (c j * ((2 : R)*z)^j)) (p-v)]
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hm)
  intro j _ hj
  simp only [Finset.mem_range, not_lt] at hj
  exact omitted_term_zero hp hj (c j) z

/-- This exact reconstruction holds at every probe, without a constant
depending on the cardinality of the probe set or degree of its extension ring.
The witness q j is the quotient after retaining the allotted base digits. -/
theorem evalSlot_eq_evalDigits {p v k g : ℕ} (hp : (2 : R)^p = 0)
    (c : Fin (p-v) → R) (d : SlotDigits p v g) (q : Fin (p-v) → R)
    (hc : ∀ j, c j = (2 : R)^(g - (j : ℕ)) *
             (((d j : ℕ) : R) + (2 : R)^width (p-v) g j * q j))
    (z : R) :
    evalSlot p v k c z = evalDigits p v k g d z := by
  simp only [evalDigits, evalSlot, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hc j, mul_pow, mul_add, add_mul, mul_add]
  suffices h : (2 : R)^v * z^k * ((2 : R)^(g - (j : ℕ)) * ((2 : R)^width (p-v) g j * q j) *
      ((2 : R)^(j : ℕ) * z^(j : ℕ))) = 0 by
    rw [h, add_zero]
  let a : ℕ := v + (g - (j : ℕ)) + width (p-v) g j + (j : ℕ)
  have hpa : p ≤ a := by
    dsimp [a, width]
    omega
  calc
    _ = (2 : R)^a * (z^(k+(j : ℕ)) * q j) := by
      dsimp only [a]
      rw [pow_add, pow_add, pow_add, pow_add]
      ring
    _ = 0 := by rw [pow_two_zero_of_le hp hpa, zero_mul]

/-- A two-local normalized coefficient has an integer numerator and an
odd integer denominator. These data suffice to construct the whole slot
message over the base ring without asking for probe-specific quotients. -/
def encodeSlot (p v g : ℕ) (num den : Fin (p-v) → ℤ) : SlotDigits p v g :=
  fun j => oddDigit (width (p-v) g j) (num j) (den j)

theorem evalSlot_eq_encodeSlot {p v k g : ℕ} (hp : (2 : R)^p = 0)
    (c normalized : Fin (p-v) → R) (num den : Fin (p-v) → ℤ)
    (hodd : ∀ j, Odd (den j))
    (hden : ∀ j, (den j : R) * normalized j = (num j : R))
    (hc : ∀ j, c j = (2 : R)^(g-(j:ℕ)) * normalized j)
    (z : R) :
    evalSlot p v k c z = evalDigits p v k g (encodeSlot p v g num den) z := by
  classical
  choose q hq using fun j : Fin (p-v) =>
    oddDigit_spec (width (p-v) g j) (num j) (den j) (hodd j) (normalized j) (hden j)
  exact evalSlot_eq_evalDigits hp c _ q (fun j => by rw [hc j, hq j]; rfl) z

/-- P7 for the truncated slot: if the extracted valuation and the gap
reach the required precision, all probes give zero. -/
theorem evalSlot_zero_of_gap {p v k g : ℕ} (hp : (2 : R)^p = 0)
    (hgap : p ≤ v+g) (c normalized : Fin (p-v) → R)
    (hc : ∀ j, c j = (2 : R)^(g-(j:ℕ)) * normalized j) (z : R) :
    evalSlot p v k c z = 0 := by
  simp only [evalSlot, Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro j _
  rw [hc j, mul_pow]
  calc
    _ = (2 : R)^(v+(g-(j:ℕ))+(j:ℕ)) * (z^(k+(j:ℕ)) * normalized j) := by
      rw [pow_add, pow_add, pow_add]; ring
    _ = 0 := by rw [pow_two_zero_of_le hp (by omega : p ≤ v+(g-(j:ℕ))+(j:ℕ)), zero_mul]

end Decode

/-- An actual menu may realize fewer messages, but not more. The output
can be a product over infinitely many probes, without a finiteness assumption
on that output type. The conclusion includes finiteness of the range. -/
theorem observed_menu_card_le {ι X Y : Type*} [Fintype ι] [DecidableEq ι]
    (p v g : ι → ℕ) (encode : X → JointDigits p v g) (decode : JointDigits p v g → Y) :
    Finite (Set.range (decode ∘ encode)) ∧
      Nat.card (Set.range (decode ∘ encode)) ≤
        2 ^ (∑ i, (triangular (p i-v i) - triangular (g i))) := by
  have hs : Set.range (decode ∘ encode) ⊆ Set.range decode := by
    rintro _ ⟨x, rfl⟩
    exact ⟨encode x, rfl⟩
  refine ⟨Finite.of_injective (Set.inclusion hs) (Set.inclusion_injective hs), ?_⟩
  have hdecode := Nat.card_le_card_of_surjective
    (Set.rangeFactorization decode) (Set.rangeFactorization_surjective (f := decode))
  rw [Nat.card_eq_fintype_card (α := JointDigits p v g), card_jointDigits] at hdecode
  exact (Nat.card_le_card_of_injective (Set.inclusion hs) (Set.inclusion_injective hs)).trans hdecode

/-- P4/P6 for the complete menu with independent output precision, valuation
gap, ring, and potentially infinite probe set at each address. The only
source hypothesis is the given power-of-two factor and two-local fraction
presentation of its normalized coefficient. -/
theorem shared_menu_budget {ι X : Type*} [Fintype ι] [DecidableEq ι]
    {R : ι → Type*} [∀ i, CommRing (R i)] {Probe : ι → Type*}
    (p v k g : ι → ℕ) (hp : ∀ i, (2 : R i)^(p i) = 0)
    (z : ∀ i, Probe i → R i)
    (c normalized : X → (i : ι) → Fin (p i-v i) → R i)
    (num den : X → (i : ι) → Fin (p i-v i) → ℤ)
    (hodd : ∀ x i j, Odd (den x i j))
    (hden : ∀ x i j, (den x i j : R i) * normalized x i j = (num x i j : R i))
    (hc : ∀ x i j, c x i j = (2 : R i)^(g i-(j:ℕ)) * normalized x i j) :
    Finite (Set.range (fun x i a => evalSlot (p i) (v i) (k i) (c x i) (z i a))) ∧
      Nat.card (Set.range (fun x i a => evalSlot (p i) (v i) (k i) (c x i) (z i a))) ≤
        2 ^ (∑ i, (triangular (p i-v i) - triangular (g i))) := by
  let encode : X → JointDigits p v g :=
    fun x i => encodeSlot (p i) (v i) (g i) (num x i) (den x i)
  let decode : JointDigits p v g → ((i : ι) → Probe i → R i) :=
    fun msg i a => evalDigits (p i) (v i) (k i) (g i) (msg i) (z i a)
  have he : (fun x i a => evalSlot (p i) (v i) (k i) (c x i) (z i a)) =
      decode ∘ encode := by
    funext x i a
    exact evalSlot_eq_encodeSlot (hp i) (c x i) (normalized x i) (num x i) (den x i)
      (hodd x i) (hden x i) (hc x i) (z i a)
  rw [he]
  exact observed_menu_card_le p v g encode decode

#print axioms sum_width
#print axioms threshold_geometric_coefficient
#print axioms weighted_jointDigits_card
#print axioms threshold_coefficient
#print axioms card_jointDigits
#print axioms omitted_term_zero
#print axioms evalSlot_eq_evalDigits
#print axioms evalSlot_eq_encodeSlot
#print axioms evalSlot_zero_of_gap
#print axioms truncateFiniteSeries
#print axioms shared_menu_budget

end PrecisionMenu

