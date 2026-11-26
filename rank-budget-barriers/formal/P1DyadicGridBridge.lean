import P1DyadicGrid
import CrossingValuation

/-!
# Source Cauchy coefficient on the integer dyadic grid

This module instantiates the generic P1/P2 multiplicative-valuation
certificate on the literal source grid and crossing port coordinates.
The valuation on a receiving characteristic-zero field is assumed to
send 2 below 1 and signed odd integers to units. A probe need only be
integral, not a unit; at zero the actual coefficient is zero.
-/

open scoped BigOperators Polynomial

namespace P1DyadicGridBridge
open P1DyadicGrid

variable {F Γ : Type*} [Field F] [CharZero F] [LinearOrderedCommGroupWithZero Γ]

omit [CharZero F] in
theorem cast_pow₂ (e : ℕ) : ((pow₂ e : ℤ):F) = (2:F)^e := by simp [pow₂]

/-- The literal C(T) product on the signed source grid. -/
def sourceNumerator (a : ℕ) (T : F) : F :=
  ∏ q ∈ grid a, (T-(q:F))

omit [CharZero F] in
theorem sourceNumerator_is_eval (a : ℕ) (T : F) :
    sourceNumerator a T = (cauchyPolynomial a).eval₂ (Int.castRingHom F) T := by
  let φ : ℤ[X] →+* F := Polynomial.eval₂RingHom (Int.castRingHom F) T
  change sourceNumerator a T = φ (cauchyPolynomial a)
  simp only [sourceNumerator, cauchyPolynomial, map_prod, map_sub]
  refine Finset.prod_congr rfl (fun q _ => ?_)
  simp [φ]

def crossingInt (t : ℤ) (x τ : ℕ) : ℤ := t-(τ:ℤ)+(x:ℤ)

noncomputable def derivRatio (a : ℕ) (t : ℤ) : F :=
  (((cauchyPolynomial a).derivative.eval t : ℤ):F) /
    (((cauchyPolynomial a).derivative.eval 0 : ℤ):F)

/-- The printed pre-moment coefficient in line 421. The omitted factor
j^b belongs to the source moment, not to this coefficient. -/
noncomputable def printedCoefficient (a i b : ℕ) (t : ℤ) (x τ : ℕ) (z : F) : F :=
  let D := ((crossingInt t x τ : ℤ):F) + (2:F)^(a+1)*z
  sourceNumerator a ((t:F)+(2:F)^(a+1)*z) /
      ((((cauchyPolynomial a).derivative.eval 0 : ℤ):F)*D)
      * ((2:F)^(i+1)/D)^b

theorem numerator_factored (a : ℕ) {t : ℤ} (ht : t ∈ grid a) (z : F) :
    sourceNumerator a ((t:F)+(2:F)^(a+1)*z) =
      (2:F)^(a+1)*z * (((cauchyPolynomial a).derivative.eval t : ℤ):F) *
        ∏ q ∈ (grid a).erase t, (1 + (2:F)^(a+1)*z/((t-q:ℤ):F)) := by
  rw [sourceNumerator,
    ← Finset.mul_prod_erase (grid a) (fun q => (t:F)+(2:F)^(a+1)*z-(q:F)) ht,
    cauchy_derivative_eval ht, Int.cast_prod, mul_assoc ((2:F)^(a+1)*z),
    ← Finset.prod_mul_distrib]
  have he (q : ℤ) (hq : q ∈ (grid a).erase t) :
    (t:F)+(2:F)^(a+1)*z-(q:F) =
      ((t-q:ℤ):F) * (1 + (2:F)^(a+1)*z/((t-q:ℤ):F)) := by
    have hqz : t-q ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hq).symm
    have hqF : ((t-q:ℤ):F) ≠ 0 := by exact_mod_cast hqz
    field_simp [hqF]
    push_cast
    ring
  have hprod := Finset.prod_congr rfl he
  rw [hprod]
  ring

theorem printedCoefficient_eq_p1 (a i b : ℕ) {t : ℤ} (ht : t ∈ grid a)
    (x τ : ℕ) (z : F) (hd : (crossingInt t x τ : F) ≠ 0)
    (hD : (crossingInt t x τ : F) + (2:F)^(a+1)*z ≠ 0) :
    printedCoefficient a i b t x τ z =
      CrossingValuation.coefficient ((grid a).erase t) (fun q => ((t-q:ℤ):F))
        2 z (derivRatio a t) (crossingInt t x τ : F) a i b := by
  rw [CrossingValuation.coefficient_eq_shifted_denominator _ _ _ _ _ _ _ _ _ hd hD]
  unfold printedCoefficient derivRatio
  dsimp only
  rw [numerator_factored a ht z]
  have h0 : (((cauchyPolynomial a).derivative.eval 0 : ℤ):F) ≠ 0 := by
    exact_mod_cast cauchy_derivative_nonzero (zero_mem_grid a)
  rw [div_pow, pow_succ _ b]
  field_simp [h0, hD]

noncomputable def oddPart (d : ℤ) : F := (d:F) / (2:F)^(padicValInt 2 d)

theorem cast_eq_oddPart (d : ℤ) :
    (d:F) = (2:F)^(padicValInt 2 d)*oddPart d := by
  unfold oddPart
  field_simp

theorem oddPart_from_int {d : ℤ} (hd : d ≠ 0) :
    ∃ w : ℤ, Odd w ∧ (oddPart d : F) = (w:F) := by
  obtain ⟨w, hw, he⟩ := integer_odd_factor hd
  refine ⟨w, hw, (div_eq_iff (pow_ne_zero _ (by norm_num : (2:F) ≠ 0))).mpr ?_⟩
  calc
    (d:F) = ((pow₂ (padicValInt 2 d)*w:ℤ):F) := congrArg (fun n : ℤ => (n:F)) he
    _ = _ := by rw [Int.cast_mul, cast_pow₂, mul_comm]

theorem oddPart_valuation (v : Valuation F Γ)
    (ho : ∀ n : ℤ, Odd n → v (n:F) = 1) {d : ℤ} (hd : d ≠ 0) :
    v (oddPart d) = 1 := by
  obtain ⟨w, hw, he⟩ := oddPart_from_int (F:=F) hd
  rw [he, ho w hw]

theorem derivRatio_valuation (v : Valuation F Γ)
    (ho : ∀ n : ℤ, Odd n → v (n:F) = 1) {a : ℕ} {t : ℤ} (ht : t ∈ grid a) :
    v (derivRatio a t) = 1 := by
  obtain ⟨k,s,r,hs,hr,hst,hr0⟩ := cauchy_derivative_common_content ht
  have hcoef (n : ℤ) : ((pow₂ k*n:ℤ):F) = (2:F)^k*(n:F) := by
    rw [Int.cast_mul, cast_pow₂]
  simp only [derivRatio, hst, hr0, hcoef, v.map_div, map_mul, ho s hs, ho r hr, mul_one]
  exact div_self (fun h => (pow_ne_zero k (by norm_num : (2:F) ≠ 0))
    ((Valuation.zero_iff v).mp h))

/-- A true exponent-a grid difference gives an odd-denominator slope in
the integral coordinate U=2z. -/
theorem grid_slope_odd_denominator {a : ℕ} {t q : ℤ}
    (ht : t ∈ grid a) (hq : q ∈ grid a) (hne : t ≠ q) :
    ∃ w : ℤ, Odd w ∧
      ((2:F)^(a+1)/((t-q:ℤ):F)) =
        2*((2:F)^(a-padicValInt 2 (t-q))/(w:F)) := by
  let e := padicValInt 2 (t-q)
  have he : e ≤ a := grid_difference_valuation_le ht hq hne
  obtain ⟨w, hw, huw⟩ := integer_odd_factor (sub_ne_zero.mpr hne)
  refine ⟨w, hw, ?_⟩
  have hu : ((t-q:ℤ):F) = (2:F)^e*(w:F) := by
    rw [show ((t-q:ℤ):F) = ((pow₂ e*w:ℤ):F) from congrArg (fun n : ℤ => (n:F)) huw,
      Int.cast_mul, cast_pow₂]
  have hwF : (w:F) ≠ 0 := by exact_mod_cast odd_int_ne_zero hw
  have hp : (2:F)^(a+1) = (2:F)^e * (2*((2:F)^(a-e))) := by
    have heq : a+1 = e+(1+(a-e)) := by omega
    nth_rw 1 [heq]
    simp only [pow_add, pow_one]
  rw [hu, hp]
  field_simp [hwF]
  rfl

/-- P2 for the source's literal Cauchy coefficient and real crossing
coordinates, not for an arbitrary family of pre-factored denominators. -/
theorem printedCoefficient_valuation (v : Valuation F Γ)
    (hsmall : v (2:F) < 1) (ho : ∀ n : ℤ, Odd n → v (n:F) = 1)
    {a i b x τ : ℕ} {t : ℤ} (ht : t ∈ grid a) (ht0 : t ≠ 0)
    (hi : padicValInt 2 t = i) (hbit : x.testBit i = τ.testBit i)
    (z : F) (hz : v z ≤ 1) :
    v (printedCoefficient a i b t x τ z) =
      (v (2:F))^(crossingExponent a i b (padicValInt 2 (crossingInt t x τ))) * v z := by
  let d := crossingInt t x τ
  let h := padicValInt 2 d
  have hi' : i ≤ a := by
    have ht' := grid_difference_valuation_le ht (zero_mem_grid a) ht0
    simpa [hi] using ht'
  have hcross : d ≠ 0 ∧ h ≤ i := crossing_nonzero_and_le ht0 hi hbit
  have hd : (d:F) ≠ 0 := by exact_mod_cast hcross.1
  have hunit : v (1+(2:F)^(a+1)*z/(d:F)) = 1 := by
    rw [cast_eq_oddPart d]
    exact CrossingValuation.normalized_shift v 2 z (oddPart d) (a+1) h
      (by norm_num) hsmall hz (oddPart_valuation v ho hcross.1) (by omega)
  have hD : (d:F)+(2:F)^(a+1)*z ≠ 0 := by
    intro hzero
    have he : 1+(2:F)^(a+1)*z/(d:F) = ((d:F)+(2:F)^(a+1)*z)/(d:F) := by
      field_simp [hd]
    rw [he, hzero, zero_div, map_zero] at hunit
    exact zero_ne_one hunit
  rw [printedCoefficient_eq_p1 a i b ht x τ z hd hD]
  have hfun : (fun q : ℤ => ((t-q:ℤ):F)) =
    (fun q => (2:F)^(padicValInt 2 (t-q))*oddPart (t-q)) :=
      funext (fun q => cast_eq_oddPart (t-q))
  rw [hfun, cast_eq_oddPart d]
  exact CrossingValuation.coefficient_valuation v ((grid a).erase t)
    (fun q => padicValInt 2 (t-q)) (fun q => oddPart (t-q))
    2 z (derivRatio a t) (oddPart d) a i h b
    (by norm_num) hsmall hz (derivRatio_valuation v ho ht) (oddPart_valuation v ho hcross.1)
    hi' hcross.2
    (fun q hq => grid_difference_valuation_le ht (Finset.mem_of_mem_erase hq)
      (Finset.ne_of_mem_erase hq).symm)
    (fun _ hq => oddPart_valuation v ho (sub_ne_zero.mpr (Finset.ne_of_mem_erase hq).symm))

theorem printedCoefficient_at_zero (a i b : ℕ) {t : ℤ} (ht : t ∈ grid a) (x τ : ℕ) :
    (printedCoefficient a i b t x τ (0:F)) = 0 := by
  rw [printedCoefficient]
  rw [numerator_factored a ht (0:F)]
  simp

#print axioms sourceNumerator_is_eval
#print axioms printedCoefficient_eq_p1
#print axioms derivRatio_valuation
#print axioms grid_slope_odd_denominator
#print axioms printedCoefficient_valuation
#print axioms printedCoefficient_at_zero

end P1DyadicGridBridge

