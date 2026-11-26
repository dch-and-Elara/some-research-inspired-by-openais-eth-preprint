import J6ActiveLocalFactor
import P1DyadicGridBridge
import Mathlib.Tactic

/-! Appendix D crossing coefficients on the literal signed grid.
C-hat is a two-local polynomial, independent of the crossing row and
column tile. B is the odd-part denominator with the even part shifted
into the visible power of two, before any receiving-ring reduction. -/
namespace J6R9PacketCoeff
open scoped BigOperators Polynomial
open Polynomial DenominatorBudget P1DyadicGrid P1DyadicGridBridge

theorem rho_twoLocal {a : ℕ} {t : ℤ} (ht : t ∈ grid a) :
    (derivRatio a t : ℚ) ∈ twoLocalSubalgebra := by
  obtain ⟨k,s,r,hs,hr,hT,h0⟩ := cauchy_derivative_common_content ht
  have ho : ¬ (2:ℤ) ∣ r := fun h => (Int.not_even_iff_odd.mpr hr) (even_iff_two_dvd.mpr h)
  refine (mem_twoLocal_iff _).mpr ⟨s,r,ho,?_⟩
  have hd : (r:ℚ) ≠ 0 := by exact_mod_cast odd_int_ne_zero hr
  have hp : (2:ℚ)^k ≠ 0 := pow_ne_zero _ (by decide)
  unfold derivRatio
  rw [hT,h0,Int.cast_mul,Int.cast_mul,cast_pow₂]
  field_simp

noncomputable def rho (a : ℕ) (t : ℤ) : TwoLocal :=
  if h : t ∈ grid a then ⟨derivRatio a t,rho_twoLocal h⟩ else 0

theorem rho_rat {a : ℕ} {t : ℤ} (ht : t ∈ grid a) :
    twoLocalRat (rho a t) = derivRatio a t := by
  rw [rho,dif_pos ht]
  rfl

noncomputable def cHat (a : ℕ) (t : ℤ) : TwoLocal[X] :=
  C (rho a t) * ∏ q ∈ (grid a).erase t, (1+C (J6ActiveLocalFactor.slope a t q)*X)

theorem cHat_eval_rat {a : ℕ} {t : ℤ} (ht : t ∈ grid a) (z : ℚ) :
    (cHat a t).eval₂ twoLocalRat z =
      (derivRatio a t : ℚ) *
        ∏ q ∈ (grid a).erase t, (1+(2:ℚ)^(a+1)*z/((t-q:ℤ):ℚ)) := by
  let E := Polynomial.eval₂RingHom twoLocalRat z
  change E (cHat a t) = _
  unfold cHat
  rw [map_mul,map_prod]
  have hR : E (C (rho a t)) = (derivRatio a t : ℚ) := by simpa [E] using rho_rat ht
  rw [hR]
  apply congrArg ((derivRatio a t : ℚ)*·)
  refine Finset.prod_congr rfl fun q hq => ?_
  have hneq := (Finset.mem_erase.mp hq).1.symm
  have hmem := (Finset.mem_erase.mp hq).2
  have hSlope :
      twoLocalRat (J6ActiveLocalFactor.slope a t q) = (2:ℚ)^(a+1)/((t:ℚ)-(q:ℚ)) := by
    rw [J6ActiveLocalFactor.slope,dif_pos ⟨ht,hmem,hneq⟩]
    rfl
  rw [map_add,map_one,map_mul]
  change 1+(C (J6ActiveLocalFactor.slope a t q)).eval₂ twoLocalRat z *
    (X : TwoLocal[X]).eval₂ twoLocalRat z = _
  rw [Polynomial.eval₂_C,Polynomial.eval₂_X,hSlope,Int.cast_sub,div_mul_eq_mul_div]

theorem normalized_numerator {a : ℕ} {t : ℤ} (ht : t ∈ grid a) (z : ℚ) :
    sourceNumerator a ((t:ℚ)+(2:ℚ)^(a+1)*z) /
        (((cauchyPolynomial a).derivative.eval 0 : ℤ):ℚ) =
      (2:ℚ)^(a+1)*z*(cHat a t).eval₂ twoLocalRat z := by
  have h0 : (((cauchyPolynomial a).derivative.eval 0 : ℤ):ℚ) ≠ 0 := by
    exact_mod_cast cauchy_derivative_nonzero (zero_mem_grid a)
  rw [numerator_factored a ht z,cHat_eval_rat ht z]
  unfold derivRatio
  field_simp

def B {R : Type*} [CommRing R] (a h : ℕ) (u : ℤ) (z : R) : R :=
  (u:R)+(2:R)^(a+1-h)*z

structure Crossing (t : ℤ) (x tile i : ℕ) where
  level : ℕ
  oddPart : ℤ
  odd : Odd oddPart
  level_le : level ≤ i
  exact_int : crossingInt t x tile = pow₂ level*oddPart
  val_eq : level = padicValInt 2 (crossingInt t x tile)

/-- Original crossing parity guarantees a genuine odd-normalization;
neither signed centers nor the boundary slot require a positivity premise. -/
noncomputable def crossingOf {t : ℤ} {x tile i : ℕ} (ht : t ≠ 0)
    (hi : padicValInt 2 t=i) (hb : x.testBit i = tile.testBit i) : Crossing t x tile i := by
  have h := crossing_nonzero_and_le ht hi hb
  change crossingInt t x tile ≠ 0 ∧ padicValInt 2 (crossingInt t x tile) ≤ i at h
  let E := integer_odd_factor h.1
  exact ⟨_,Classical.choose E,(Classical.choose_spec E).1,h.2,
    (Classical.choose_spec E).2,rfl⟩

theorem denominator_normalized {a i : ℕ} {t : ℤ} {x tile : ℕ}
    (hi : i ≤ a) (d : Crossing t x tile i) (z : ℚ) :
    ((crossingInt t x tile:ℤ):ℚ)+(2:ℚ)^(a+1)*z =
      (2:ℚ)^d.level * B a d.level d.oddPart z := by
  rw [d.exact_int,Int.cast_mul,cast_pow₂,B,mul_add,← mul_assoc,← pow_add]
  rw [Nat.add_sub_of_le (d.level_le.trans (hi.trans (Nat.le_succ _)))]

/-- Literal Appendix D (crossing expansion) coefficient after one extracts
the true power of two from the denominator. -/
theorem printed_coefficient {a i : ℕ} {t : ℤ} {x tile : ℕ}
    (ht : t ∈ grid a) (hi : i ≤ a) (d : Crossing t x tile i) (z : ℚ) (b : ℕ)
    (hB : B a d.level d.oddPart z ≠ 0) :
    printedCoefficient (F:=ℚ) a i b t x tile z =
      ((2:ℚ)^(a+1-d.level)*z*(cHat a t).eval₂ twoLocalRat z /
        B a d.level d.oddPart z) *
      (((2:ℚ)^(i+1-d.level)) / B a d.level d.oddPart z)^b := by
  have h0 : (((cauchyPolynomial a).derivative.eval 0 : ℤ):ℚ) ≠ 0 := by
    exact_mod_cast cauchy_derivative_nonzero (zero_mem_grid a)
  have hh : (2:ℚ)^d.level ≠ 0 := pow_ne_zero _ (by decide)
  have hA : (2:ℚ)^(a+1)=(2:ℚ)^d.level*(2:ℚ)^(a+1-d.level) := by
    rw [← pow_add,Nat.add_sub_of_le (d.level_le.trans (hi.trans (Nat.le_succ _)))]
  have hI : (2:ℚ)^(i+1)=(2:ℚ)^d.level*(2:ℚ)^(i+1-d.level) := by
    rw [← pow_add,Nat.add_sub_of_le (d.level_le.trans (Nat.le_succ _))]
  unfold printedCoefficient
  dsimp only
  rw [← div_div,normalized_numerator ht z,denominator_normalized hi d z]
  have hr : (2:ℚ)^(i+1)/((2:ℚ)^d.level*B a d.level d.oddPart z) =
      (2:ℚ)^(i+1-d.level)/B a d.level d.oddPart z := by
    rw [hI]
    field_simp
  rw [hr]
  congr 1
  rw [hA]
  field_simp

#print axioms rho_twoLocal
#print axioms cHat_eval_rat
#print axioms normalized_numerator
#print axioms crossingOf
#print axioms denominator_normalized
#print axioms printed_coefficient
end J6R9PacketCoeff
