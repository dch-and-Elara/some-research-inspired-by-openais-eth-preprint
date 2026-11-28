import Mathlib.Data.Nat.Choose.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Ideal.Basic

/-! Multivariate Newton evaluations on integer grid nodes, normalized
Newton products at arbitrary distinct field nodes, and the minimum common
denominator for a finite set of Smith coordinates. The factorial valuation
at general DVR digit nodes, jet Taylor features, and existence of the
corresponding Smith presentation are separate mathematical steps. -/

set_option autoImplicit false
set_option warningAsError true

namespace NewtonCapacity

open scoped BigOperators

variable {R E I X Y : Type*}

section Grid

variable [CommRing R] [Fintype E]

/-- The integral, normalized Newton basis on ordinary nonnegative nodes. -/
def binomialValue (degree point : E → ℕ) : R :=
  ∏ e, ((point e).choose (degree e) : R)

/-- The monic Newton functions on the same nodes. -/
def fallingValue (degree point : E → ℕ) : R :=
  ∏ e, ((point e).descFactorial (degree e) : R)

def factorialWeight (degree : E → ℕ) : R :=
  ∏ e, ((degree e).factorial : R)

theorem falling_eq_weight_mul (degree point : E → ℕ) :
    fallingValue (R := R) degree point =
      factorialWeight degree * binomialValue degree point := by
  simp only [fallingValue, factorialWeight, binomialValue,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, Finset.prod_mul_distrib]

theorem binomial_self (degree : E → ℕ) :
    binomialValue (R := R) degree degree = 1 := by
  simp [binomialValue]

theorem binomial_vanish (degree point : E → ℕ) (e : E) (he : point e < degree e) :
    binomialValue (R := R) degree point = 0 := by
  classical
  apply Finset.prod_eq_zero (Finset.mem_univ e)
  simp [Nat.choose_eq_zero_of_lt he]

def gridMatrix (degree : I → E → ℕ) : Matrix I I R :=
  Matrix.of fun row col => binomialValue (degree col) (degree row)

variable [Fintype I] [LinearOrder I]

/-- The index order extends the coordinate order on the chosen grid.
This applies to an arbitrary finite list of distinct multi-indices in any
linear extension. No rank or determinant hypothesis is used. -/
theorem grid_det (degree : I → E → ℕ)
    (order : ∀ i j, (∀ e, degree i e ≤ degree j e) → i ≤ j) :
    (gridMatrix (R := R) degree).det = 1 := by
  classical
  have ht : (gridMatrix (R := R) degree).BlockTriangular OrderDual.toDual := by
    intro i j hij
    change i < j at hij
    have hn : ¬ ∀ e, degree j e ≤ degree i e := fun h => (not_le_of_gt hij) (order j i h)
    push_neg at hn
    obtain ⟨e, he⟩ := hn
    exact binomial_vanish _ _ e he
  rw [Matrix.det_of_lowerTriangular _ ht]
  simp [gridMatrix, binomial_self]

def evaluation (degree : I → E → ℕ) (c : I → R) (x : E → ℕ) : R :=
  ∑ i, binomialValue (degree i) x * c i

omit [LinearOrder I] in
theorem grid_mulVec (degree : I → E → ℕ) (c : I → R) (i : I) :
    (gridMatrix degree).mulVec c i = evaluation degree c (degree i) := rfl

/-- Value divisibility on a finite Newton grid forces coefficient
divisibility, for any ideal of any commutative coefficient ring. -/
theorem grid_ideal_iff (degree : I → E → ℕ)
    (order : ∀ i j, (∀ e, degree i e ≤ degree j e) → i ≤ j)
    (J : Ideal R) (c : I → R) :
    (∀ i, evaluation degree c (degree i) ∈ J) ↔ ∀ i, c i ∈ J := by
  classical
  constructor
  · intro hv i
    let M := gridMatrix (R := R) degree
    have hdet : IsUnit M.det := by
      change IsUnit (gridMatrix (R := R) degree).det
      rw [grid_det degree order]
      exact isUnit_one
    have hi : M⁻¹.mulVec (M.mulVec c) = c := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hdet, Matrix.one_mulVec]
    rw [← hi]
    exact J.sum_mem (fun j _ => J.mul_mem_left _ (hv j))
  · intro hc i
    exact J.sum_mem (fun j _ => J.mul_mem_left _ (hc j))

/-- The grid certifies membership on every integer tuple, even when the
coefficient ring has nilpotents. -/
theorem all_values_ideal_iff (degree : I → E → ℕ)
    (order : ∀ i j, (∀ e, degree i e ≤ degree j e) → i ≤ j)
    (J : Ideal R) (c : I → R) :
    (∀ x, evaluation degree c x ∈ J) ↔ ∀ i, c i ∈ J := by
  constructor
  · intro hx
    exact (grid_ideal_iff degree order J c).1 (fun i => hx (degree i))
  · intro hc x
    exact J.sum_mem (fun j _ => J.mul_mem_left _ (hc j))

omit [LinearOrder I] in
theorem weighted_matrix_factorization (degree : I → E → ℕ) (point : X → E → ℕ)
    (coeff : Matrix I Y R) :
    (Matrix.of fun x y => ∑ i, fallingValue (degree i) (point x) * coeff i y) =
      (Matrix.of fun x i => binomialValue (degree i) (point x)) *
        (Matrix.of fun i y => factorialWeight (degree i) * coeff i y) := by
  ext x y
  simp only [Matrix.of_apply, Matrix.mul_apply, falling_eq_weight_mul]
  apply Finset.sum_congr rfl
  intro i _
  ac_rfl

end Grid

section Rank

variable {K : Type*} [Field K] [Fintype E] [Fintype I] [LinearOrder I] [Fintype Y]

/-- On the witness grid the rank is exactly that of the weighted
coefficient matrix. This polynomial evaluation statement uses field rank. -/
theorem weighted_grid_rank (degree : I → E → ℕ)
    (order : ∀ i j, (∀ e, degree i e ≤ degree j e) → i ≤ j)
    (coeff : Matrix I Y K) :
    (Matrix.of fun x y => ∑ i, fallingValue (degree i) (degree x) * coeff i y).rank =
      (Matrix.of fun i y => factorialWeight (degree i) * coeff i y).rank := by
  rw [weighted_matrix_factorization]
  apply Matrix.rank_mul_eq_right_of_isUnit_det
  change IsUnit (gridMatrix (R := K) degree).det
  rw [grid_det degree order]
  exact isUnit_one

end Rank

section ArbitraryNodes

variable {K : Type*} [Field K]

/-- Monic univariate Newton polynomial evaluated at a field element. -/
def nodeProduct (node : ℕ → K) (n : ℕ) (x : K) : K :=
  ∏ j ∈ Finset.range n, (x - node j)

def nodeRatio (node : ℕ → K) (n : ℕ) (x : K) : K :=
  nodeProduct node n x / nodeProduct node n (node n)

theorem node_diagonal_ne_zero (node : ℕ → K) (distinct : Function.Injective node) (n : ℕ) :
    nodeProduct node n (node n) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr ?_
  intro j hj
  exact sub_ne_zero.mpr (fun he => (Nat.ne_of_lt (Finset.mem_range.mp hj)) (distinct he).symm)

theorem node_ratio_self (node : ℕ → K) (distinct : Function.Injective node) (n : ℕ) :
    nodeRatio node n (node n) = 1 := by
  exact div_self (node_diagonal_ne_zero node distinct n)

theorem node_ratio_below (node : ℕ → K) {i n : ℕ} (hi : i < n) :
    nodeRatio node n (node i) = 0 := by
  have hn : nodeProduct node n (node i) = 0 := by
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hi) (sub_self (node i))
  simp only [nodeRatio, hn, zero_div]

variable [Fintype E] [Fintype I] [LinearOrder I]

def ratioGrid (node : ℕ → K) (degree : I → E → ℕ) : Matrix I I K :=
  Matrix.of fun i j => ∏ e, nodeRatio node (degree j e) (node (degree i e))

/-- The determinant-one property works on digit-ordered nodes in an
arbitrary fraction field. The diagonal normalization uses its full
nonzero value, so its diagonal entries are exactly one. -/
theorem ratio_grid_det (node : ℕ → K) (distinct : Function.Injective node)
    (degree : I → E → ℕ) (order : ∀ i j, (∀ e, degree i e ≤ degree j e) → i ≤ j) :
    (ratioGrid node degree).det = 1 := by
  classical
  have ht : (ratioGrid node degree).BlockTriangular OrderDual.toDual := by
    intro i j hij
    change i < j at hij
    have hn : ¬ ∀ e, degree j e ≤ degree i e := fun h => (not_le_of_gt hij) (order j i h)
    push_neg at hn
    obtain ⟨e, he⟩ := hn
    exact Finset.prod_eq_zero (Finset.mem_univ e) (node_ratio_below node he)
  rw [Matrix.det_of_lowerTriangular _ ht]
  simp [ratioGrid, node_ratio_self node distinct]

/-- Given the integral evaluations established by the separate fixed-divisor
argument, they form an invertible matrix over the integral coefficient ring
itself. The determinant and any rank conclusion are proved from the grid. -/
theorem integral_ratio_grid_det [CommRing R] (embed : R →+* K)
    (faithful : Function.Injective embed) (node : ℕ → K) (distinct : Function.Injective node)
    (degree : I → E → ℕ) (order : ∀ i j, (∀ e, degree i e ≤ degree j e) → i ≤ j)
    (M : Matrix I I R) (entries : ∀ i j, embed (M i j) = ratioGrid node degree i j) :
    M.det = 1 := by
  apply faithful
  rw [map_one, RingHom.map_det]
  have hm : embed.mapMatrix M = ratioGrid node degree := by
    ext i j
    exact entries i j
  rw [hm, ratio_grid_det node distinct degree order]

end ArbitraryNodes

section Denominators

variable [CommRing R] [IsDomain R]

/-- Removing a common denominator in an integral coordinate is
truncated subtraction of its exponent. -/
theorem cancel_power_debt (π : R) (hπ : π ≠ 0) (s L : ℕ) (v : R) :
    π ^ s ∣ π ^ L * v ↔ π ^ (s - L) ∣ v := by
  rcases le_total L s with h | h
  · have hs : s = L + (s - L) := (Nat.add_sub_of_le h).symm
    conv_lhs => lhs; rw [hs, pow_add]
    exact mul_dvd_mul_iff_left (pow_ne_zero _ hπ)
  · have hsl : s - L = 0 := Nat.sub_eq_zero_of_le h
    rw [hsl, pow_zero]
    exact iff_of_true ((pow_dvd_pow π h).trans (dvd_mul_right _ _)) (one_dvd _)

/-- A scalar target modulo π^p in a Smith direction of exponent s can
be lifted at loss L exactly when the appropriate power divides it. -/
theorem diagonal_precision_membership (π : R) (hπ : π ≠ 0) (s L p : ℕ) (v : R) :
    (∃ e : R, π ^ s ∣ π ^ L * (v + π ^ p * e)) ↔
      π ^ min p (s - L) ∣ v := by
  constructor
  · rintro ⟨e, he⟩
    have h1 := (cancel_power_debt π hπ s L _).1 he
    have h2 := (pow_dvd_pow π (min_le_right p (s - L))).trans h1
    have h3 := (pow_dvd_pow π (min_le_left p (s - L))).trans (dvd_mul_right _ e)
    simpa only [add_sub_cancel_right] using dvd_sub h2 h3
  · intro hv
    rcases le_total (s - L) p with h | h
    · rw [min_eq_right h] at hv
      refine ⟨0, (cancel_power_debt π hπ s L _).2 ?_⟩
      simpa only [mul_zero, add_zero] using hv
    · rw [min_eq_left h] at hv
      rcases hv with ⟨t, ht⟩
      refine ⟨-t, ?_⟩
      simp [ht]

/-- Zero target coordinates impose no loss. A nonzero coordinate of
order t costs the excess of its Smith exponent over t. -/
def demand (p s t : ℕ) : ℕ := if t < p then s - t else 0

theorem loss_for_one_order (π : R) (hπ : π ≠ 0) (s L p t : ℕ) (v : R)
    (order : ∀ n ≤ p, (π ^ n ∣ v ↔ n ≤ t)) :
    (∃ e : R, π ^ s ∣ π ^ L * (v + π ^ p * e)) ↔ demand p s t ≤ L := by
  rw [diagonal_precision_membership π hπ, order _ (min_le_left _ _)]
  unfold demand
  split <;> omega

/-- The least common loss across any finite collection of Smith coordinate
and target-column pairs is their maximum demand. Orders are supplied by
their divisibility characterization, with no loss hypothesis. -/
theorem minimum_common_loss [Fintype I] (π : R) (hπ : π ≠ 0)
    (p L : ℕ) (s t : I → ℕ) (v : I → R)
    (order : ∀ i, ∀ n ≤ p, (π ^ n ∣ v i ↔ n ≤ t i)) :
    (∀ i, ∃ e : R, π ^ (s i) ∣ π ^ L * (v i + π ^ p * e)) ↔
      Finset.univ.sup (fun i => demand p (s i) (t i)) ≤ L := by
  classical
  rw [Finset.sup_le_iff]
  simp only [Finset.mem_univ, forall_true_left]
  exact forall_congr' fun i => loss_for_one_order π hπ _ _ _ _ _ (order i)

end Denominators

/-- Outside the fraction-field span of the raw image, a zero numerator
realizes precisely the zero target class. This holds at every loss. -/
theorem outside_direction_iff [CommRing R] (π v : R) (p : ℕ) :
    (∃ e : R, v + π ^ p * e = 0) ↔ π ^ p ∣ v := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨-e, ?_⟩
    rw [mul_neg]
    exact eq_neg_of_add_eq_zero_left he
  · rintro ⟨t, ht⟩
    exact ⟨-t, by simp [ht]⟩

#print axioms falling_eq_weight_mul
#print axioms binomial_self
#print axioms binomial_vanish
#print axioms grid_det
#print axioms grid_mulVec
#print axioms grid_ideal_iff
#print axioms all_values_ideal_iff
#print axioms weighted_matrix_factorization
#print axioms weighted_grid_rank
#print axioms node_diagonal_ne_zero
#print axioms node_ratio_self
#print axioms node_ratio_below
#print axioms ratio_grid_det
#print axioms integral_ratio_grid_det
#print axioms cancel_power_debt
#print axioms diagonal_precision_membership
#print axioms loss_for_one_order
#print axioms minimum_common_loss
#print axioms outside_direction_iff

end NewtonCapacity
