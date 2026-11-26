import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Nat.Prime.Int
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Tactic

/-!
# Denominator budget for polynomial decoding (S5)

A polynomial over any commutative ring preserves congruence modulo any
ideal. If a denominator-cleared decoder is integral, input congruence
modulo the q-th power of a regular element implies output congruence
modulo the (q - pole)-th power. An embedding into a larger ring permits
the original decoder to have rational coefficients.
-/

namespace DenominatorBudget

open MvPolynomial

section Ring

variable {R ι : Type*} [CommRing R]

/-- No assumption on a degree bound or even on the size of the variable
index type is needed. A multivariate polynomial has finite support. -/
theorem eval_sub_mem_ideal (I : Ideal R) (P : MvPolynomial ι R) {x y : ι → R}
    (h : ∀ i, x i-y i ∈ I) : P.eval x-P.eval y ∈ I := by
  induction P using MvPolynomial.induction_on with
  | C r =>
    simpa only [eval_C, sub_self] using I.zero_mem
  | add P Q hP hQ =>
    simp only [map_add]
    convert I.add_mem hP hQ using 1
    ring
  | mul_X P i hP =>
    simp only [eval_mul, eval_X]
    convert I.add_mem (I.mul_mem_left (x i) hP) (I.mul_mem_left (P.eval y) (h i)) using 1
    ring

theorem eval_dvd_sub (base : R) (P : MvPolynomial ι R) {x y : ι → R}
    (h : ∀ i, base ∣ x i-y i) : base ∣ P.eval x-P.eval y := by
  rw [← Ideal.mem_span_singleton]
  exact eval_sub_mem_ideal _ P (fun i => Ideal.mem_span_singleton.mpr (h i))

/-- Enough cancellation for the lower bound, even in rings with other
zero divisors. -/
theorem mul_pow_injective {a : R} (ha : Function.Injective (a * · : R → R)) (k : ℕ) :
    Function.Injective (a^k * · : R → R) := by
  induction k with
  | zero => simpa using Function.injective_id
  | succ k ih =>
    intro u v huv
    apply ih
    apply ha
    simpa only [pow_succ', mul_assoc] using huv

/-- Strong output congruence. Here the integral polynomial P represents
the original decoder multiplied by a common clearing power. -/
theorem output_dvd_of_cleared {a u w : R}
    (ha : Function.Injective (a * · : R → R)) (q pole : ℕ)
    (P : MvPolynomial ι R) {x y : ι → R} (h : ∀ i, a^q ∣ x i-y i)
    (hx : P.eval x = a^pole * u) (hy : P.eval y = a^pole * w) :
    a^(q-pole) ∣ u-w := by
  by_cases hq : q ≤ pole
  · simp [Nat.sub_eq_zero_of_le hq]
  · have hp : pole ≤ q := by omega
    obtain ⟨z, hz⟩ := eval_dvd_sub (a^q) P h
    refine ⟨z, mul_pow_injective ha pole ?_⟩
    have he : a^q = a^pole*a^(q-pole) := by
      rw [← pow_add, Nat.add_sub_of_le hp]
    calc
      a^pole*(u-w) = P.eval x-P.eval y := by rw [hx, hy, mul_sub]
      _ = a^q*z := hz
      _ = a^pole*(a^(q-pole)*z) := by rw [he, mul_assoc]

/-- If the recovered values differ already modulo a, the pole exponent
must be at least q. -/
theorem pole_of_cleared {a u w : R}
    (ha : Function.Injective (a * · : R → R)) (q pole : ℕ)
    (P : MvPolynomial ι R) {x y : ι → R} (h : ∀ i, a^q ∣ x i-y i)
    (hx : P.eval x = a^pole * u) (hy : P.eval y = a^pole * w)
    (hdistinct : ¬ a ∣ u-w) :
    q ≤ pole := by
  by_contra hn
  have h1 : 1 ≤ q-pole := by omega
  exact hdistinct ((show a ∣ a^(q-pole) from by
    simpa only [pow_one] using (pow_dvd_pow a h1)).trans
      (output_dvd_of_cleared ha q pole P h hx hy))

end Ring

section Extension

variable {R S ι : Type*} [CommRing R] [CommRing S]

/-- A coefficient-by-coefficient integrality certificate gives a single
finite multivariate polynomial over the base ring. -/
theorem exists_base_polynomial_of_coefficients (f : R →+* S) (P : MvPolynomial ι S)
    (hc : ∀ i, P.coeff i ∈ Set.range f) :
    ∃ Q : MvPolynomial ι R, MvPolynomial.map f Q = P := by
  apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
  intro c hc'
  obtain ⟨i, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc'
  exact hc i

/-- An algebraic denominator-clearing equality gives the exact power-of-a
congruence for the integral outputs, even when the numerator polynomial
is plugged into a larger ring. -/
theorem output_dvd_of_scaled_coefficients (f : R →+* S) (hf : Function.Injective f)
    {a u w : R} (ha : Function.Injective (a * · : R → R)) (q pole : ℕ)
    (H : MvPolynomial ι S) {x y : ι → R} (h : ∀ i, a^q ∣ x i-y i)
    (hc : ∀ i, (C ((f a)^pole) * H).coeff i ∈ Set.range f)
    (hx : H.eval (f ∘ x) = f u) (hy : H.eval (f ∘ y) = f w) :
    a^(q-pole) ∣ u-w := by
  obtain ⟨P, hP⟩ := exists_base_polynomial_of_coefficients f _ hc
  have heval (z : ι → R) (v : R) (hz : H.eval (f ∘ z) = f v) :
      P.eval z = a^pole*v := by
    apply hf
    rw [eval₂_comp, ← eval_map, hP, eval_mul, eval_C, hz, map_mul, map_pow]
  exact output_dvd_of_cleared ha q pole P h (heval x u hx) (heval y w hy)

/-- S5 stated using only coefficientwise integrality, an injective
extension, and regularity of the denominator base. -/
theorem pole_of_scaled_coefficients (f : R →+* S) (hf : Function.Injective f)
    {a u w : R} (ha : Function.Injective (a * · : R → R)) (q pole : ℕ)
    (H : MvPolynomial ι S) {x y : ι → R} (h : ∀ i, a^q ∣ x i-y i)
    (hc : ∀ i, (C ((f a)^pole) * H).coeff i ∈ Set.range f)
    (hx : H.eval (f ∘ x) = f u) (hy : H.eval (f ∘ y) = f w)
    (hdistinct : ¬ a ∣ u-w) :
    q ≤ pole := by
  by_contra hn
  have h1 : 1 ≤ q-pole := by omega
  exact hdistinct ((show a ∣ a^(q-pole) from by
    simpa only [pow_one] using (pow_dvd_pow a h1)).trans
      (output_dvd_of_scaled_coefficients f hf ha q pole H h hc hx hy))

end Extension

section TwoLocal

/-- The prime at two in the integers. -/
def atTwoPrime : Ideal ℤ := Ideal.span ({2} : Set ℤ)

instance : atTwoPrime.IsPrime := by
  exact (Ideal.span_singleton_prime (show (2:ℤ) ≠ 0 by norm_num)).mpr
    (Nat.prime_iff_prime_int.mp Nat.prime_two)

/-- The localization at two, realized as a subalgebra of the rationals. -/
noncomputable def twoLocalSubalgebra : Subalgebra ℤ ℚ :=
  Localization.subalgebra.ofField ℚ atTwoPrime.primeCompl atTwoPrime.primeCompl_le_nonZeroDivisors

abbrev TwoLocal := ↥twoLocalSubalgebra

/-- The rational embedding of the two-local integers. -/
noncomputable def twoLocalRat : TwoLocal →+* ℚ := twoLocalSubalgebra.val.toRingHom

theorem twoLocalRat_injective : Function.Injective twoLocalRat := Subtype.val_injective

theorem mem_twoLocal_iff (x : ℚ) :
    x ∈ twoLocalSubalgebra ↔ ∃ n d : ℤ, ¬ (2:ℤ) ∣ d ∧ x = (n:ℚ)/(d:ℚ) := by
  change
    (∃ (n d : ℤ) (_ : d ∈ atTwoPrime.primeCompl),
      x = algebraMap ℤ ℚ n * (algebraMap ℤ ℚ d)⁻¹) ↔ _
  simp only [atTwoPrime, Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton,
    algebraMap_int_eq, div_eq_mul_inv]
  constructor <;> rintro ⟨n, d, hd, hx⟩ <;> exact ⟨n, d, hd, hx⟩

/-- Localization at odd denominators preserves the parity of an integer. -/
theorem two_dvd_intCast_iff (n : ℤ) :
    (2:TwoLocal) ∣ (n:TwoLocal) ↔ (2:ℤ) ∣ n := by
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨r, d, hd, hw'⟩ := (mem_twoLocal_iff (w:ℚ)).mp w.property
    have hd0 : d ≠ 0 := fun hz => hd (hz ▸ dvd_zero (2:ℤ))
    have hdq : (d:ℚ) ≠ 0 := by exact_mod_cast hd0
    have he : (n:ℚ) = 2 * ((r:ℚ)/(d:ℚ)) := by
      have hq := congrArg twoLocalRat hw
      rw [map_intCast, map_mul, map_ofNat, show twoLocalRat w = (w:ℚ) from rfl, hw'] at hq
      exact hq
    have hi : n*d = 2*r := by
      exact_mod_cast (show (n:ℚ)*(d:ℚ) = 2*(r:ℚ) by rw [he, mul_assoc, div_mul_cancel₀ _ hdq])
    exact ((Nat.prime_iff_prime_int.mp Nat.prime_two).dvd_mul.mp ⟨r, hi⟩).resolve_right hd
  · rintro ⟨z, rfl⟩
    exact ⟨(z:TwoLocal), by push_cast; rfl⟩

/-- Literal S5 with observations and cleared coefficients in the
two-local integers, a rational polynomial, and integer outputs of
distinct parity. No instance or regularity assumption is passed in. -/
theorem s5_twoLocal {ι : Type*} (q pole : ℕ) (H : MvPolynomial ι ℚ)
    {x y : ι → TwoLocal} (h : ∀ i, (2:TwoLocal)^q ∣ x i-y i)
    (hc : ∀ i, (C ((2:ℚ)^pole) * H).coeff i ∈ twoLocalSubalgebra)
    {u w : ℤ} (hx : H.eval (fun i => (x i:ℚ)) = (u:ℚ))
    (hy : H.eval (fun i => (y i:ℚ)) = (w:ℚ))
    (hparity : ¬ (2:ℤ) ∣ u-w) :
    q ≤ pole := by
  have hregular : Function.Injective ((2:TwoLocal)*· : TwoLocal → TwoLocal) := by
    intro a b hEq
    apply twoLocalRat_injective
    have hm := congrArg twoLocalRat hEq
    rw [map_mul, map_mul, map_ofNat] at hm
    exact mul_left_cancel₀ (by norm_num : (2:ℚ) ≠ 0) hm
  apply pole_of_scaled_coefficients twoLocalRat twoLocalRat_injective hregular q pole H h
      (u := (u:TwoLocal)) (w := (w:TwoLocal))
  · intro i
    rw [map_ofNat]
    exact ⟨⟨_, hc i⟩, rfl⟩
  · change H.eval (fun i => (x i : ℚ)) = twoLocalRat (u:TwoLocal)
    rw [map_intCast]
    exact hx
  · change H.eval (fun i => (y i : ℚ)) = twoLocalRat (w:TwoLocal)
    rw [map_intCast]
    exact hy
  · intro hd
    apply hparity
    apply (two_dvd_intCast_iff (u-w)).mp
    push_cast
    exact hd

/-- The exponent q is attainable already with one variable and a linear
decoder. Its two observations are 2^q and 0 and its outputs are 1 and 0. -/
theorem s5_linear_sharp (q : ℕ) :
    ∃ H : MvPolynomial Unit ℚ,
      (∀ i, (C ((2:ℚ)^q) * H).coeff i ∈ twoLocalSubalgebra) ∧
      H.eval (fun _ => (2:ℚ)^q) = 1 ∧ H.eval (fun _ => 0) = 0 := by
  let H : MvPolynomial Unit ℚ := C (((2:ℚ)^q)⁻¹) * X ()
  have h2 : (2:ℚ)^q ≠ 0 := pow_ne_zero _ (by norm_num)
  refine ⟨H, ?_, ?_, ?_⟩
  · intro i
    have hc : C ((2:ℚ)^q) * H = X () := by
      dsimp [H]
      rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ h2, map_one, one_mul]
    rw [hc, MvPolynomial.X, coeff_monomial]
    split <;> simp
  · simp [H, eval_mul]
  · simp [H]

end TwoLocal

#print axioms eval_sub_mem_ideal
#print axioms output_dvd_of_cleared
#print axioms exists_base_polynomial_of_coefficients
#print axioms output_dvd_of_scaled_coefficients
#print axioms pole_of_scaled_coefficients
#print axioms two_dvd_intCast_iff
#print axioms s5_twoLocal
#print axioms s5_linear_sharp

end DenominatorBudget

