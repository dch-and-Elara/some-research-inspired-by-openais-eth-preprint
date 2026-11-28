import AOracleSuccinctPacket
import AOracleSuccinctKernel
import AOracleCoordinates

/-!
# A1 recipes generated from physical records

With a supplied packing, bounded original local tables, and the actual
node/probe, the A1 verifier below evaluates legal coefficient cells
from the normalized signed dyadic formula. The packing is not found
or certified by this file. To match the source claim, the input mode
list must represent all eligible addresses without duplicates and
eligible row/tile pairs must satisfy the source crossing bit condition.
-/

open scoped BigOperators Polynomial

namespace AOracleSuccinctPhysical
open AOracleSuccinct AOracleSuccinctPacket AOracleSuccinctNative AOracleSuccinctKernel
open P1DyadicGrid AOracleWitness AOracleThreshold

def oddPartsAt (a : ℕ) (t : ℤ) : ℤ :=
  ∏ q ∈ (grid a).erase t, oddWord (t-q)

theorem oddPartsAt_odd (a : ℕ) (t : ℤ) : Odd (oddPartsAt a t) := by
  apply prod_odd
  intro q hq
  exact (oddWord_factor (sub_ne_zero.mpr (Finset.ne_of_mem_erase hq).symm)).1

theorem normalized_derivative_ratio {F : Type*} [Field F] [CharZero F]
    {a : ℕ} {t : ℤ} (ht : t ∈ grid a) :
    (P1DyadicGridBridge.derivRatio a t : F) = (oddPartsAt a t:F)/(oddDerivative a:F) := by
  have hh := product_exact ht (0:F) ((grid a).erase t) (fun _ h => h)
  simp only [mul_zero, add_zero, normFactor, shiftWord] at hh
  unfold P1DyadicGridBridge.derivRatio
  rw [cauchy_derivative_eval ht, Int.cast_prod]
  simp only [Int.cast_sub]
  rw [hh, derivative_factored ht,
    mul_div_mul_left _ _ (pow_ne_zero _ (by norm_num))]
  rw [oddPartsAt, Int.cast_prod]

/-- The algebraic cells can be generated without any assignment data.
This version of the crossing value uses one inverse per normalized
grid odd word, one shifted odd inverse, and the odd derivative inverse. -/
def crossCell {R : Type*} [CommRing R] (p a i b : ℕ)
    (t : ℤ) (x τ : ℕ) (z : R) : R :=
  let d := P1DyadicGridBridge.crossingInt t x τ
  let h := padicValInt 2 d
  ((oddPartsAt a t:R)*oddInverse p (oddDerivative a:R)) *
    (2:R)^(crossingExponent a i b h)*z *
    (∏ q ∈ (grid a).erase t, (1+(2:R)^(a+1-padicValInt 2 (t-q))*z *
      oddInverse p (oddWord (t-q):R))) *
    (oddInverse p (shiftWord (oddWord d) (a+1-h) z))^(b+1)

/-- This finite-ring equation is the normalized native coefficient,
with unit denominators only. The target oddness proof uses the signed
real Cauchy/grid crossing geometry, not an assumed abstract unit. -/
theorem crossCell_denominator {R : Type*} [CommRing R] (p a i b : ℕ)
    (hp : (2:R)^p=0) {t : ℤ} (ht : t ∈ grid a) (ht0 : t ≠ 0)
    (hi : padicValInt 2 t = i) (x τ : ℕ) (hbit : x.testBit i = τ.testBit i)
    (z : R) :
    let d := P1DyadicGridBridge.crossingInt t x τ
    let h := padicValInt 2 d
    let D := shiftWord (oddWord d) (a+1-h) z
    ((oddDerivative a:R)*D^(b+1))*crossCell p a i b t x τ z =
      (2:R)^(crossingExponent a i b h)*z*(∏ q ∈ (grid a).erase t, normFactor a t q z) := by
  dsimp only
  let d := P1DyadicGridBridge.crossingInt t x τ
  let h := padicValInt 2 d
  let D := shiftWord (oddWord d) (a+1-h) z
  let ps := ∏ q ∈ (grid a).erase t, (1+(2:R)^(a+1-padicValInt 2 (t-q))*z*
      oddInverse p (oddWord (t-q):R))
  have hgeo : d ≠ 0 ∧ h ≤ i := crossing_nonzero_and_le ht0 hi hbit
  have ha : i ≤ a := by
    simpa [hi] using grid_difference_valuation_le ht (zero_mem_grid a) ht0
  have hD : D * oddInverse p D = 1 :=
    inverse_shift p _ hp (by have := hgeo.2; omega) _ ((oddWord_factor hgeo.1).1) z
  have hDP : D^(b+1)*(oddInverse p D)^(b+1)=1 := by rw [← mul_pow, hD, one_pow]
  have hder := inverse_int p hp _ (oddDerivative_odd a)
  have hgrid : (oddPartsAt a t:R)*ps = ∏ q ∈ (grid a).erase t, normFactor a t q z := by
    unfold oddPartsAt ps
    rw [Int.cast_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro q hq
    have ho := (oddWord_factor (sub_ne_zero.mpr (Finset.ne_of_mem_erase hq).symm)).1
    have hinv := inverse_int p hp _ ho
    let w := ((oddWord (t-q):ℤ):R)
    let v := (2:R)^(a+1-padicValInt 2 (t-q))*z
    change w*(1+v*oddInverse p w) = w+v
    rw [show w*(1+v*oddInverse p w)=w+v*(w*oddInverse p w) by ring, hinv, mul_one]
  change ((oddDerivative a:R)*D^(b+1))*
      ((((oddPartsAt a t:R)*oddInverse p (oddDerivative a:R)) *
      (2:R)^(crossingExponent a i b h)*z*ps) * (oddInverse p D)^(b+1)) = _
  calc
    _ = ((oddDerivative a:R)*oddInverse p (oddDerivative a:R)) *
        (D^(b+1)*(oddInverse p D)^(b+1)) *
        ((2:R)^(crossingExponent a i b h)*z) * ((oddPartsAt a t:R)*ps) := by ring
    _ = _ := by rw [hder, hDP, one_mul, one_mul, hgrid]

theorem literal_slot_difference {a : ℕ} (x y : Fin (2^a)) :
    (y.val:ℤ)-(x.val:ℤ) ∈ grid a := by
  rw [mem_grid]
  have hx : (x.val:ℤ) < pow₂ a := by
    simpa [pow₂] using (show (x.val:ℤ)<((2^a:ℕ):ℤ) from by exact_mod_cast x.isLt)
  have hy : (y.val:ℤ) < pow₂ a := by
    simpa [pow₂] using (show (y.val:ℤ)<((2^a:ℕ):ℤ) from by exact_mod_cast y.isLt)
  omega

section Finite
variable {p : ℕ}
open AOracleCoordinates

theorem double_quotient_two_nilpotent (f : (Base p)[X]) (ell : ℕ) :
    (2:Truncated f ell)^p=0 := by
  let h := (AdjoinRoot.of ((Polynomial.X:(AdjoinRoot f)[X])^ell)).comp (AdjoinRoot.of f)
  have hz : (2:Base p)^p=0 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using ZMod.natCast_self (2^p)
  simpa only [map_pow, map_ofNat, map_zero] using congrArg h hz

noncomputable def physical {r c m packets G a i delta ell : ℕ} (f : (Base p)[X])
    (rt : List (BoolTensor r delta)) (ct : List (BoolTensor c delta))
    (row : Ports r packets G (2^a)) (col : Ports c packets G (2^a))
    (modes : Fin m → Mode packets G i p) (t : ℤ) (z : Truncated f ell) :
    Recipes (Truncated f ell) r c m delta :=
  compile rt ct row col modes
    (fun j k => modular p a t (((col.slot k).val:ℤ)-((row.slot j).val:ℤ)) z)
    (fun j mode => crossCell p a i mode.exponent.val t
      (row.slot j).val mode.tile.val z)

/-- Exact coefficient count for the above deliberately explicit
finite verifier. This does not establish source layout admissibility
or a formal Turing-machine implementation of all bit costs. -/
theorem physical_coefficient {r c m packets G a i delta ell b : ℕ} (f : (Base p)[X])
    (rt : List (BoolTensor r delta)) (ct : List (BoolTensor c delta))
    (row : Ports r packets G (2^a)) (col : Ports c packets G (2^a))
    (modes : Fin m → Mode packets G i p) (t : ℤ) (z : Truncated f ell)
    (beta : Fin m →₀ ℕ) (coord : Truncated f ell →+ Base p) (fits : m+1 ≤ 2^b) :
    (countVerify (fun zc : Code r c b × Word p =>
        accept (physical f rt ct row col modes t z) beta coord zc.1 zc.2) : Base p) =
      coord (MvPolynomial.coeff beta
        (rootPolynomial (rootTerms (physical f rt ct row col modes t z)))) :=
  coefficient_coordinate _ _ _ fits

end Finite

#print axioms oddPartsAt_odd
#print axioms normalized_derivative_ratio
#print axioms literal_slot_difference
#print axioms crossCell_denominator
#print axioms double_quotient_two_nilpotent
#print axioms physical_coefficient

end AOracleSuccinctPhysical

