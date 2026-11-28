import FiniteMoments
import BangCore
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.Order.Field.Basic

/-! Finite product-coordinate variance and transfer to a dominated rational
law. Coordinate orthogonality is proved by splitting one factor off the
actual assignment space. -/

namespace ProductVariance

open scoped BigOperators

variable {I A X : Type*} [Fintype I] [Fintype A] [Fintype X]

/-- The weight of one point of a finite uniform law. -/
def uniformWeight (X : Type*) [Fintype X] : ℚ := (Fintype.card X : ℚ)⁻¹

/-- A finite rational uniform expectation. -/
def uniformMean (f : X → ℚ) : ℚ := uniformWeight X * ∑ x, f x

private theorem card_ne_zero [Nonempty X] : (Fintype.card X : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr Fintype.card_ne_zero

private theorem weight_nonneg (X : Type*) [Fintype X] : 0 ≤ uniformWeight X :=
  inv_nonneg.mpr (Nat.cast_nonneg _)

private theorem card_mul_mean [Nonempty X] (f : X → ℚ) :
    (Fintype.card X : ℚ) * uniformMean f = ∑ x, f x := by
  rw [uniformMean, uniformWeight, ← mul_assoc, mul_inv_cancel₀ card_ne_zero, one_mul]

private theorem sum_weight (X : Type*) [Fintype X] [Nonempty X] :
    (∑ _x : X, uniformWeight X) = 1 := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, uniformWeight]
  exact mul_inv_cancel₀ card_ne_zero

private theorem sum_centered [Nonempty X] (f : X → ℚ) :
    (∑ x, (f x - uniformMean f)) = 0 := by
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    card_mul_mean, sub_self]

private theorem mean_sum {J : Type*} [Fintype J] (g : J → X → ℚ) :
    uniformMean (fun x => ∑ j, g j x) = ∑ j, uniformMean (g j) := by
  simp only [uniformMean]
  rw [Finset.sum_comm, Finset.mul_sum]

section Product

variable [DecidableEq I] [Nonempty A]

/-- Under the uniform law on assignments, coordinate i is uniform on A. -/
theorem coordinate_mean (i : I) (f : A → ℚ) :
    uniformMean (fun x : I → A => f (x i)) = uniformMean f := by
  classical
  let rest := {k : I // k ≠ i} → A
  let split := Equiv.funSplitAt i A
  have hc : (∑ x : I → A, (f (x i) - uniformMean f)) = 0 := by
    calc
      _ = ∑ z : A × rest, (f z.1 - uniformMean f) :=
        split.sum_comp (fun z => f z.1 - uniformMean f)
      _ = _ := by
        rw [Fintype.sum_prod_type_right]
        simp only [sum_centered, Finset.sum_const_zero]
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hc
  apply mul_left_cancel₀ (card_ne_zero (X := I → A))
  rw [card_mul_mean]
  linarith only [hc]

omit [Nonempty A] in
/-- Distinct coordinate functions have zero product expectation whenever the
first one has mean zero on the alphabet. -/
theorem distinct_coordinate_orthogonality (i j : I) (hij : i ≠ j) (u v : A → ℚ)
    (hu : ∑ a, u a = 0) :
    uniformMean (fun x : I → A => u (x i) * v (x j)) = 0 := by
  classical
  let rest := {k : I // k ≠ i} → A
  let j' : {k : I // k ≠ i} := ⟨j, hij.symm⟩
  let split := Equiv.funSplitAt i A
  have hsum : (∑ x : I → A, u (x i) * v (x j)) = 0 := by
    calc
      _ = ∑ z : A × rest, u z.1 * v (z.2 j') :=
        split.sum_comp (fun z => u z.1 * v (z.2 j'))
      _ = _ := by
        rw [Fintype.sum_prod_type_right]
        simp only [← Finset.sum_mul, hu, zero_mul, Finset.sum_const_zero]
  rw [uniformMean, hsum, mul_zero]

/-- Variance of the sum of independent one-coordinate functions equals the
sum of their variances under the uniform product law. -/
theorem uniform_product_variance (g : I → A → ℚ) :
    uniformMean (fun x : I → A => (∑ i, (g i (x i) - uniformMean (g i))) ^ 2) =
      ∑ i, uniformMean (fun a => (g i a - uniformMean (g i)) ^ 2) := by
  classical
  let u (i : I) (a : A) := g i a - uniformMean (g i)
  have hzero (i : I) : (∑ a, u i a) = 0 := sum_centered (g i)
  have hx (x : I → A) :
      (∑ i, u i (x i)) ^ 2 = ∑ i, ∑ j, u i (x i) * u j (x j) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  change uniformMean (fun x : I → A => (∑ i, u i (x i)) ^ 2) =
    ∑ i, uniformMean (fun a => u i a ^ 2)
  simp only [hx, mean_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = uniformMean (fun x : I → A => u i (x i) * u i (x i)) := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact distinct_coordinate_orthogonality i j hji.symm (u i) (u j) (hzero i)
      · simp
    _ = uniformMean (fun a => u i a * u i a) := coordinate_mean i (fun a => u i a * u i a)
    _ = _ := by simp only [pow_two]

end Product

/-- For a scalar bounded by R, its uniform variance is at most R². -/
theorem uniform_variance_le_square [Nonempty A] (f : A → ℚ) (R : ℚ) (hR : ∀ a, |f a| ≤ R) :
    uniformMean (fun a => (f a - uniformMean f) ^ 2) ≤ R ^ 2 := by
  classical
  have hR0 : 0 ≤ R := (abs_nonneg (f (Classical.arbitrary A))).trans (hR _)
  have hs (a : A) : f a ^ 2 ≤ R ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (f a)) hR0).mpr (hR a)
  have hz : (∑ a, uniformWeight A * (f a - uniformMean f)) = 0 := by
    rw [← Finset.mul_sum, sum_centered, mul_zero]
  have hv := FiniteMoments.centered_square_le (fun _ : A => uniformWeight A)
    (fun a => f a - uniformMean f) (-uniformMean f) (sum_weight A) hz
  simp only [sub_neg_eq_add, sub_add_cancel] at hv
  calc
    _ = ∑ a, uniformWeight A * (f a - uniformMean f) ^ 2 := by rw [uniformMean, Finset.mul_sum]
    _ ≤ ∑ a, uniformWeight A * f a ^ 2 := hv
    _ ≤ ∑ _a : A, uniformWeight A * R ^ 2 :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hs a) (weight_nonneg A))
    _ = _ := by rw [← Finset.sum_mul, sum_weight, one_mul]

/-- Variance under an arbitrary law dominated by C times the uniform product
law. Each g_i is bounded by R_i on the alphabet. The centering is the mean
under μ, which may differ from the product mean. -/
theorem dominated_coordinate_variance [DecidableEq I] [Nonempty A]
    (μ : (I → A) → ℚ) (g : I → A → ℚ) (R : I → ℚ) (C : ℚ)
    (hmass : ∑ x, μ x = 1) (hC : 0 ≤ C)
    (hdom : ∀ x, μ x ≤ C * uniformWeight (I → A)) (hR : ∀ i a, |g i a| ≤ R i) :
    (∑ x, μ x * ((∑ i, g i (x i)) - ∑ y, μ y * ∑ i, g i (y i)) ^ 2) ≤
      C * ∑ i, R i ^ 2 := by
  let Y (x : I → A) := ∑ i, g i (x i)
  let m := ∑ x, μ x * Y x
  let t := ∑ i, uniformMean (g i)
  have hz : (∑ x, μ x * (Y x - m)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hmass, one_mul]
    exact sub_self m
  have htrans := FiniteMoments.dominated_centered_second_moment μ (fun _ => uniformWeight (I → A))
    (fun x => Y x - m) C (t - m) hmass hz hdom
  have hd (x : I → A) : (Y x - m) - (t - m) = ∑ i, (g i (x i) - uniformMean (g i)) := by
    rw [Finset.sum_sub_distrib]
    dsimp only [Y, t]
    ring
  simp only [hd, ← Finset.mul_sum] at htrans
  calc
    _ ≤ C * uniformMean (fun x : I → A => (∑ i, (g i (x i) - uniformMean (g i))) ^ 2) := htrans
    _ = C * ∑ i, uniformMean (fun a => (g i a - uniformMean (g i)) ^ 2) := by
      rw [uniform_product_variance]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun i _ => uniform_variance_le_square (g i) (R i) (hR i))) hC

section Grouped

variable {J : Type*} [Fintype J] [DecidableEq I] [Nonempty A]

/-- Number of listed functions depending on coordinate i. -/
def coordinateCount (owner : J → I) (i : I) : ℕ :=
  (Finset.univ.filter fun j => owner j = i).card

/-- Center a coordinate function using its mean under the possibly nonproduct law μ. -/
def centeredCoordinate (μ : (I → A) → ℚ) (owner : J → I) (values : J → A → ℚ)
    (j : J) (x : I → A) : ℚ :=
  values j (x (owner j)) - ∑ y, μ y * values j (y (owner j))

/-- For every sign vector, the joint second moment of the centered list is at
most C times the sum of the squared coordinate multiplicities. Values in
[-1,1] include the event indicators of the cut theorem. -/
theorem signed_centered_coordinate_moment (μ : (I → A) → ℚ) (owner : J → I)
    (values : J → A → ℚ) (C : ℚ) (hmass : ∑ x, μ x = 1) (hC : 0 ≤ C)
    (hdom : ∀ x, μ x ≤ C * uniformWeight (I → A)) (hbound : ∀ j a, |values j a| ≤ 1)
    (eps : J → Bool) :
    (∑ x, μ x * (BangCore.signedTotal (centeredCoordinate μ owner values) eps x) ^ 2) ≤
      C * ∑ i, (coordinateCount owner i : ℚ) ^ 2 := by
  classical
  let fiber (i : I) := Finset.univ.filter fun j => owner j = i
  let g (i : I) (a : A) := ∑ j ∈ fiber i, BangCore.bitSign (eps j) * values j a
  have hsign (s : Bool) : |BangCore.bitSign s| = 1 := by cases s <;> norm_num [BangCore.bitSign]
  have hR (i : I) (a : A) : |g i a| ≤ (coordinateCount owner i : ℚ) := by
    calc
      _ ≤ ∑ j ∈ fiber i, |BangCore.bitSign (eps j) * values j a| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ fiber i, (1 : ℚ) := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [abs_mul, hsign, one_mul] using hbound j a
      _ = _ := by simp [fiber, coordinateCount]
  have hraw (x : I → A) : (∑ i, g i (x i)) =
      ∑ j, BangCore.bitSign (eps j) * values j (x (owner j)) := by
    calc
      _ = ∑ i, ∑ j ∈ fiber i, BangCore.bitSign (eps j) * values j (x (owner j)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j hj
        rw [(Finset.mem_filter.mp hj).2]
      _ = _ := Finset.sum_fiberwise Finset.univ owner _
  have hlinear : (∑ y, μ y * ∑ j, BangCore.bitSign (eps j) * values j (y (owner j))) =
      ∑ j, BangCore.bitSign (eps j) * ∑ y, μ y * values j (y (owner j)) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hc (x : I → A) : BangCore.signedTotal (centeredCoordinate μ owner values) eps x =
      (∑ i, g i (x i)) - ∑ y, μ y * ∑ i, g i (y i) := by
    simp only [hraw, hlinear, BangCore.signedTotal, centeredCoordinate, mul_sub,
      Finset.sum_sub_distrib]
  simp only [hc]
  exact dominated_coordinate_variance μ g (fun i => (coordinateCount owner i : ℚ))
    C hmass hC hdom hR

end Grouped

#print axioms coordinate_mean
#print axioms distinct_coordinate_orthogonality
#print axioms uniform_product_variance
#print axioms uniform_variance_le_square
#print axioms dominated_coordinate_variance
#print axioms signed_centered_coordinate_moment

end ProductVariance
