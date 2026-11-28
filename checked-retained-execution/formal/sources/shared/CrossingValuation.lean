
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic

namespace CrossingValuation
open scoped BigOperators
variable {F Γ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ]

theorem normalized_shift (v : Valuation F Γ) (π z d₀ : F) (a h : ℕ)
    (hπ : π ≠ 0) (hsmall : v π < 1) (hz : v z ≤ 1) (hd : v d₀ = 1)
    (hah : h < a) : v (1 + π ^ a * z / (π ^ h * d₀)) = 1 := by
  have hd0 : d₀ ≠ 0 := by intro he; simp [he] at hd
  have he : π ^ a * z / (π ^ h * d₀) = π ^ (a - h) * z / d₀ := by
    nth_rw 1 [show a = h + (a - h) by omega]
    rw [pow_add]
    field_simp
  rw [he]
  have hb : v (π ^ (a-h) * z / d₀) < v 1 := by
    rw [v.map_div, map_mul, map_pow, hd, div_one, map_one]
    calc
      v π ^ (a-h) * v z ≤ v π ^ (a-h) * 1 := mul_le_mul_left' hz _
      _ = _ := mul_one _
      _ < 1 := pow_lt_one₀ zero_le' hsmall (by omega)
  exact (v.map_add_eq_of_lt_left hb).trans (map_one v)

variable {J : Type*} 

/-- P1 as a finite rational product. -/
def coefficient (grid : Finset J) (d : J → F) (π z c target : F) (a i b : ℕ) : F :=
  c * (π ^ (a+1) * (π ^ (i+1)) ^ b / target ^ (b+1)) * z *
    (∏ j ∈ grid, (1 + π ^ (a+1) * z / d j)) /
      (1 + π ^ (a+1) * z / target) ^ (b+1)

theorem coefficient_zero (grid : Finset J) (d : J → F) (π c target : F) (a i b : ℕ) :
    coefficient grid d π 0 c target a i b = 0 := by
  simp [coefficient]

/-- P2 exact multiplicative valuation, instantiated with uniformizer 2 in
    the dyadic application. The grid differences are given in unit form. -/
theorem coefficient_valuation (v : Valuation F Γ) (grid : Finset J)
    (e : J → ℕ) (d₀ : J → F) (π z c target₀ : F) (a i h b : ℕ)
    (hπ : π ≠ 0) (hs : v π < 1) (hz : v z ≤ 1)
    (hc : v c = 1) (ht : v target₀ = 1)
    (hi : i ≤ a) (hh : h ≤ i)
    (he : ∀ j ∈ grid, e j ≤ a) (hd : ∀ j ∈ grid, v (d₀ j) = 1) :
    v (coefficient grid (fun j => π ^ e j * d₀ j) π z c (π ^ h * target₀) a i b)
      = v π ^ (a+1-i + b+(b+1)*(i-h)) * v z := by
  have H : v (∏ j ∈ grid, (1 + π ^ (a+1) * z / (π ^ e j * d₀ j))) = 1 := by
    rw [map_prod]
    exact Finset.prod_eq_one fun j hj =>
      normalized_shift v π z (d₀ j) (a+1) (e j) hπ hs hz (hd j hj) (by have := he j hj; omega)
  have Ht := normalized_shift v π z target₀ (a+1) h hπ hs hz ht (by omega)
  simp only [coefficient, v.map_div, map_mul, map_pow, H, Ht, hc, ht, one_pow, div_one,
    one_mul, mul_one, ← pow_mul, ← pow_add]
  have hn : v π ≠ 0 := fun hh' => hπ ((Valuation.zero_iff v).mp hh')
  have hex : a + 1 + (i+1)*b =
      (a+1-i + b+(b+1)*(i-h)) + h*(b+1) := by
    have h1 : a+1-i+i = a+1 := by omega
    have h2 : i-h+h = i := by omega
    calc
      a+1+(i+1)*b = (a+1-i+i)+(i+1)*b := congrArg (fun x => x+(i+1)*b) h1.symm
      _ = (a+1-i)+b+(b+1)*i := by ring
      _ = (a+1-i)+b+(b+1)*(i-h+h) := congrArg (fun x => (a+1-i)+b+(b+1)*x) h2.symm
      _ = _ := by ring
  rw [hex, pow_add, mul_div_cancel_right₀ _ (pow_ne_zero _ hn)]

/-- For each degree b the exact coefficient of the finite geometric expansion
    of the crossing denominator is the normalized P1 coefficient. -/
theorem coefficient_eq_shifted_denominator (grid : Finset J) (d : J → F)
    (π z c target : F) (a i b : ℕ)
    (h : target ≠ 0) (hshift : target + π ^ (a+1) * z ≠ 0) :
    coefficient grid d π z c target a i b =
      (c * π ^ (a+1) * z * ∏ j ∈ grid, (1 + π ^ (a+1) * z / d j)) *
      (π ^ (i+1)) ^ b / (target + π ^ (a+1) * z) ^ (b+1) := by
  have he : 1 + π ^ (a+1) * z / target = (target + π ^ (a+1) * z) / target := by
    field_simp
  rw [coefficient, he, div_pow]
  field_simp

/-- Exact finite expansion with remainder; no analytic convergence, or
    completion of a local coefficient ring, is needed for this identity. -/
theorem finite_crossing_expansion (C D x : F) (hD : D ≠ 0) (h : D - x ≠ 0) (n : ℕ) :
    C / (D - x) =
      (∑ b ∈ Finset.range n, C * x ^ b / D ^ (b+1)) +
        C * x ^ n / (D ^ n * (D - x)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have hstep : C * x ^ n / (D ^ n * (D - x)) =
        C * x ^ n / D ^ (n+1) +
          C * x ^ (n+1) / (D ^ (n+1) * (D - x)) := by
      rw [pow_succ D n, pow_succ x n]
      field_simp
      ring
    rw [hstep, add_assoc]

#print axioms coefficient_eq_shifted_denominator
#print axioms finite_crossing_expansion

#print axioms normalized_shift
#print axioms coefficient_valuation
end CrossingValuation

