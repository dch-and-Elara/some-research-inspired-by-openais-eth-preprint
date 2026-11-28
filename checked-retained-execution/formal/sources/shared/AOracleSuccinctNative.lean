import P1DyadicGridBridge
import V9BitCostInterpolation
import Mathlib.Tactic

/-!
# On-demand native shifted-odd arithmetic for a prescribed A1 register

The crossing coefficient is evaluated by the literal normalized
dyadic formula. Its ring inverses are computed by a finite recurrence
using oddness, effective even when the ring has zero divisors.
The exact source identity over characteristic zero is separate from
the finite evaluation of the normalized expression.
-/

open scoped BigOperators Polynomial

namespace AOracleSuccinctNative
open P1DyadicGrid P1DyadicGridBridge V9BitCostInterpolation

/-- Signed odd part, computed by exact integer division. -/
def oddWord (n : ℤ) : ℤ := n / pow₂ (padicValInt 2 n)

theorem oddWord_factor {n : ℤ} (hn : n ≠ 0) :
    Odd (oddWord n) ∧ n = pow₂ (padicValInt 2 n)*oddWord n := by
  obtain ⟨w, hw, he⟩ := integer_odd_factor hn
  have hv : oddWord n = w := by
    have hd := pow₂_pos (padicValInt 2 n)
    unfold oddWord
    nth_rw 1 [he]
    rw [Int.mul_ediv_cancel_left _ hd.ne']
  rw [hv]
  exact ⟨hw,he⟩

section Ring
variable {R : Type*} [CommRing R]

/-- p updates solve x*y=1 whenever x reduces to one mod two. -/
def oddInverse (p : ℕ) (x : R) : R := correction (1-x) p

theorem oddInverse_correct (p : ℕ) (hp : (2:R)^p=0) (x : R)
    (hx : ∃ y : R, x=1+2*y) : x*oddInverse p x=1 := by
  obtain ⟨y,hy⟩ := hx
  have hh : 1-x*1 = 2*(-y) := by rw [hy]; ring
  simpa only [mul_one, one_mul, oddInverse] using
    (inverse_from_residue x 1 (-y) p hh hp)

theorem shifted_odd (w : ℤ) (hw : Odd w) (k : ℕ) (hk : 0<k) (z : R) :
    ∃ y : R, (w:R)+(2:R)^k*z = 1+2*y := by
  obtain ⟨j,hj⟩ := hw
  refine ⟨(j:R)+(2:R)^(k-1)*z,?_⟩
  have he : k = k-1+1 := by omega
  nth_rw 1 [he]
  rw [pow_succ,hj]
  push_cast
  ring

def shiftWord (w : ℤ) (k : ℕ) (z : R) : R := (w:R)+(2:R)^k*z

theorem inverse_shift (p k : ℕ) (hp : (2:R)^p=0) (hk : 0<k)
    (w : ℤ) (hw : Odd w) (z : R) :
    shiftWord w k z * oddInverse p (shiftWord w k z) = 1 :=
  oddInverse_correct p hp _ (shifted_odd w hw k hk z)

theorem inverse_int (p : ℕ) (hp : (2:R)^p=0) (w : ℤ) (hw : Odd w) :
    (w:R)*oddInverse p (w:R)=1 := by
  simpa [shiftWord] using inverse_shift p 1 hp (by decide) w hw (0:R)

/-- For an input normalized list, one shifted odd inverse of the
target is reused b+1 times. Each remaining denominator is integer
odd; all inversions take exactly p recurrence updates. -/
def normalizedCross (p E k b : ℕ) (s r w : ℤ)
    (gridWords : List (ℤ × ℕ)) (z : R) : R :=
  ((s:R)*oddInverse p (r:R)) * (2:R)^E*z *
    (gridWords.map (fun qe => 1+(2:R)^qe.2*z*oddInverse p (qe.1:R))).prod *
    (oddInverse p (shiftWord w k z))^(b+1)

end Ring

section Source
variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
theorem shift_scale {a h : ℕ} (hh : h ≤ a) (w : ℤ) (z : F) :
    (2:F)^h*((w:F)+(2:F)^(a+1-h)*z) =
      (2:F)^h*(w:F)+(2:F)^(a+1)*z := by
  rw [mul_add, ← mul_assoc, ← pow_add, show h+(a+1-h)=a+1 by omega]

/-- Exact crossing expression before modular reduction. Written with
only odd grid reciprocals, one shifted odd reciprocal, and the
known explicit power of two. This is line 421, not the whole mode. -/
theorem printed_eq_normalized {a i b : ℕ} {t : ℤ} (ht : t ∈ grid a)
    (x τ : ℕ) (z : F) (hh : padicValInt 2 (crossingInt t x τ) ≤ i)
    (hi : i ≤ a) (hd : crossingInt t x τ ≠ 0)
    (hshift : shiftWord (oddWord (crossingInt t x τ))
        (a+1-padicValInt 2 (crossingInt t x τ)) z ≠ 0) :
    printedCoefficient a i b t x τ z =
      derivRatio a t * (2:F)^(crossingExponent a i b
        (padicValInt 2 (crossingInt t x τ))) * z *
        (∏ q ∈ (grid a).erase t, (1+(2:F)^(a+1-padicValInt 2 (t-q))*z /
          (oddWord (t-q):F))) /
        (shiftWord (oddWord (crossingInt t x τ))
          (a+1-padicValInt 2 (crossingInt t x τ)) z)^(b+1) := by
  let d := crossingInt t x τ
  let h := padicValInt 2 d
  let D := shiftWord (oddWord d) (a+1-h) z
  have hdF : (d:F) ≠ 0 := by exact_mod_cast hd
  have hD : D ≠ 0 := hshift
  have hd' : (d:F) = (2:F)^h*(oddWord d:F) := by
    have hhF := congrArg (fun j : ℤ => (j:F)) (oddWord_factor hd).2
    simpa only [Int.cast_mul, P1DyadicGridBridge.cast_pow₂] using hhF
  have hscale : (d:F)+(2:F)^(a+1)*z = (2:F)^h*D := by
    rw [hd']
    exact (shift_scale (hh.trans hi) _ _).symm
  have hnon : (d:F)+(2:F)^(a+1)*z ≠ 0 := by
    rw [hscale]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hD
  rw [printedCoefficient_eq_p1 a i b ht x τ z hdF hnon,
    CrossingValuation.coefficient_eq_shifted_denominator _ _ _ _ _ _ _ _ _ hdF hnon]
  change (derivRatio a t * (2:F)^(a+1)*z * (∏ q ∈ (grid a).erase t,
      (1+(2:F)^(a+1)*z/((t-q:ℤ):F)))) * ((2:F)^(i+1))^b /
      ((d:F)+(2:F)^(a+1)*z)^(b+1) = _
  have hprod :
      (∏ q ∈ (grid a).erase t, (1+(2:F)^(a+1)*z/((t-q:ℤ):F))) =
       ∏ q ∈ (grid a).erase t, (1+(2:F)^(a+1-padicValInt 2 (t-q))*z /
          (oddWord (t-q):F)) := by
    apply Finset.prod_congr rfl
    intro q hq
    have hne : t ≠ q := (Finset.ne_of_mem_erase hq).symm
    have hv := grid_difference_valuation_le ht (Finset.mem_of_mem_erase hq) hne
    have hx : t-q ≠ 0 := sub_ne_zero.mpr hne
    have hf : ((t-q:ℤ):F) = (2:F)^(padicValInt 2 (t-q))*(oddWord (t-q):F) := by
      have hhF := congrArg (fun j : ℤ => (j:F)) (oddWord_factor hx).2
      simpa only [Int.cast_mul, P1DyadicGridBridge.cast_pow₂] using hhF
    have hk : (oddWord (t-q):F) ≠ 0 := by
      exact_mod_cast odd_int_ne_zero ((oddWord_factor hx).1)
    have hp : (2:F)^(a+1) = (2:F)^(padicValInt 2 (t-q)) *
        (2:F)^(a+1-padicValInt 2 (t-q)) := by
      rw [← pow_add, show padicValInt 2 (t-q)+(a+1-padicValInt 2 (t-q))=a+1 by omega]
    rw [hp]
    apply congrArg (fun v : F => 1+v)
    rw [hf, mul_assoc, mul_div_mul_left _ _ (pow_ne_zero _ (by norm_num))]
  rw [hprod, hscale, mul_pow, ← pow_mul, ← pow_mul]
  have hsum := crossing_exponent_balance (b:=b) hi hh
  have he : (2:F)^(a+1) * (2:F)^((i+1)*b) =
      (2:F)^(crossingExponent a i b h) * (2:F)^(h*(b+1)) := by
    rw [← pow_add, ← pow_add, hsum]
  change _ = derivRatio a t * (2:F)^(crossingExponent a i b h) * z *
    (∏ q ∈ (grid a).erase t, (1+(2:F)^(a+1-padicValInt 2 (t-q))*z /
      (oddWord (t-q):F))) / D^(b+1)
  field_simp [hD]
  linear_combination (norm := ring) he *
    (derivRatio a t*z * (∏ q ∈ (grid a).erase t,
      (1+(2:F)^(a+1-padicValInt 2 (t-q))*z/(oddWord (t-q):F))))

end Source

#print axioms oddWord_factor
#print axioms oddInverse_correct
#print axioms inverse_shift
#print axioms inverse_int
#print axioms printed_eq_normalized

end AOracleSuccinctNative

