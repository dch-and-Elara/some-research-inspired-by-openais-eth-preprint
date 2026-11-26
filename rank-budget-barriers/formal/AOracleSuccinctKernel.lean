import AOracleSuccinctNative

/-!
# Actual Cauchy kernel by cancellation on the signed dyadic grid

Same-packet coefficients use the literal product with the one
\(q=y-x\) factor omitted before evaluation. Both branches below are
valid at zero probe. The modular algorithm never attempts to invert
an even coefficient or to divide by the unreduced mesh denominator.
-/

open scoped BigOperators Polynomial

namespace AOracleSuccinctKernel
open P1DyadicGrid P1DyadicGridBridge AOracleSuccinctNative

def normFactor {R : Type*} [CommRing R] (a : ℕ) (t q : ℤ) (z : R) : R :=
  shiftWord (oddWord (t-q)) (a+1-padicValInt 2 (t-q)) z

def oddDerivative (a : ℕ) : ℤ :=
  ∏ q ∈ (grid a).erase 0, oddWord (0-q)

theorem prod_odd {J : Type*} (s : Finset J) (f : J → ℤ) (hs : ∀ x ∈ s, Odd (f x)) :
    Odd (∏ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (hs a (Finset.mem_insert_self _ _)).mul
      (ih (fun x hx => hs x (Finset.mem_insert_of_mem hx)))

theorem oddDerivative_odd (a : ℕ) : Odd (oddDerivative a) := by
  apply prod_odd
  intro q hq
  exact (oddWord_factor (sub_ne_zero.mpr (Finset.ne_of_mem_erase hq).symm)).1

section
variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
theorem factor_exact {a : ℕ} {t q : ℤ} (ht : t ∈ grid a) (hq : q ∈ (grid a).erase t) (z : F) :
    (t:F)+(2:F)^(a+1)*z-(q:F) =
      (2:F)^(padicValInt 2 (t-q))*normFactor a t q z := by
  have hne : t ≠ q := (Finset.ne_of_mem_erase hq).symm
  have hq' := grid_difference_valuation_le ht (Finset.mem_of_mem_erase hq) hne
  have hF := congrArg (fun j : ℤ => (j:F)) (oddWord_factor (sub_ne_zero.mpr hne)).2
  simp only [Int.cast_mul, P1DyadicGridBridge.cast_pow₂, Int.cast_sub] at hF
  rw [normFactor, shiftWord, shift_scale hq', ← hF]
  ring

omit [CharZero F] in
theorem product_exact {a : ℕ} {t : ℤ} (ht : t ∈ grid a) (z : F)
    (s : Finset ℤ) (hs : s ⊆ (grid a).erase t) :
    (∏ q ∈ s, ((t:F)+(2:F)^(a+1)*z-(q:F))) =
      (2:F)^(∑ q ∈ s, padicValInt 2 (t-q))*∏ q ∈ s, normFactor a t q z := by
  rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun q hq => factor_exact ht (hs hq) z)

omit [CharZero F] in
theorem derivative_factored {a : ℕ} {t : ℤ} (ht : t ∈ grid a) :
    (((cauchyPolynomial a).derivative.eval 0 : ℤ):F) =
      (2:F)^(∑ q ∈ (grid a).erase t, padicValInt 2 (t-q))*(oddDerivative a:F) := by
  have h0 := product_exact (zero_mem_grid a) (0:F) ((grid a).erase 0) (fun _ h => h)
  simp only [Int.cast_zero, mul_zero, add_zero, normFactor, shiftWord, zero_sub] at h0
  rw [cauchy_derivative_eval (zero_mem_grid a), Int.cast_prod, oddDerivative, Int.cast_prod]
  rw [sum_grid_difference_valuations ht, ← sum_grid_difference_valuations (zero_mem_grid a)]
  simpa using h0

/-- Source polynomial C(T)/(C'(0)(T-k)) interpreted by omission,
so no division by a zero probe factor occurs. -/
noncomputable def actual (a : ℕ) (t k : ℤ) (z : F) : F :=
  (∏ q ∈ (grid a).erase k, ((t:F)+(2:F)^(a+1)*z-(q:F))) /
    (((cauchyPolynomial a).derivative.eval 0 : ℤ):F)

theorem actual_normalized_same {a : ℕ} {t : ℤ} (ht : t ∈ grid a) (z : F) :
    actual a t t z = (∏ q ∈ (grid a).erase t, normFactor a t q z)/(oddDerivative a:F) := by
  unfold actual
  rw [product_exact ht z _ (fun _ h => h), derivative_factored ht,
    mul_div_mul_left _ _ (pow_ne_zero _ (by norm_num))]

/-- For k ≠ t omit that normalized factor and retain just one residual
power of two and the (possibly zero) probe coordinate. -/
theorem actual_normalized_other {a : ℕ} {t k : ℤ} (ht : t ∈ grid a) (hk : k ∈ grid a)
    (hne : t ≠ k) (z : F) :
    actual a t k z =
      ((2:F)^(a+1-padicValInt 2 (t-k))*z *
        ∏ q ∈ ((grid a).erase t).erase k, normFactor a t q z)/(oddDerivative a:F) := by
  have htin : t ∈ (grid a).erase k := Finset.mem_erase.mpr ⟨hne,ht⟩
  have hkin : k ∈ (grid a).erase t := Finset.mem_erase.mpr ⟨hne.symm,hk⟩
  let s := ((grid a).erase t).erase k
  have hs : s ⊆ (grid a).erase t := Finset.erase_subset _ _
  have hval := grid_difference_valuation_le ht hk hne
  have hsum : (∑ q ∈ (grid a).erase t, padicValInt 2 (t-q)) =
      padicValInt 2 (t-k) + ∑ q ∈ s, padicValInt 2 (t-q) := by
    exact (Finset.add_sum_erase _ _ hkin).symm
  have her : ((grid a).erase k).erase t = s := by
    ext q
    simp only [s, Finset.mem_erase]
    tauto
  unfold actual
  rw [← Finset.mul_prod_erase ((grid a).erase k)
    (fun q => (t:F)+(2:F)^(a+1)*z-(q:F)) htin,
    show (t:F)+(2:F)^(a+1)*z-(t:F) = (2:F)^(a+1)*z by ring,
    her, product_exact ht z s hs, derivative_factored ht, hsum,
    pow_add (2:F) (padicValInt 2 (t-k)) (∑ q ∈ s, padicValInt 2 (t-q))]
  have hp : (2:F)^(a+1) = (2:F)^(padicValInt 2 (t-k)) *
      (2:F)^(a+1-padicValInt 2 (t-k)) := by
    rw [← pow_add, show padicValInt 2 (t-k)+(a+1-padicValInt 2 (t-k))=a+1 by omega]
  rw [hp]
  field_simp
  ring

end

/-- Actual finite-ring recipe for the source kernel. The field proofs
above certify normalization before reducing; the inverse below is
certified in the finite residue ring, including zero divisors. -/
def modular {R : Type*} [CommRing R] (p a : ℕ) (t k : ℤ) (z : R) : R :=
  let d := oddInverse p (oddDerivative a:R)
  if k=t then (∏ q ∈ (grid a).erase t, normFactor a t q z)*d
  else (2:R)^(a+1-padicValInt 2 (t-k))*z *
    (∏ q ∈ ((grid a).erase t).erase k, normFactor a t q z)*d

theorem modular_denominator {R : Type*} [CommRing R] (p a : ℕ) (hp : (2:R)^p=0)
    (t k : ℤ) (z : R) :
    (oddDerivative a:R)*modular p a t k z =
      if k=t then ∏ q ∈ (grid a).erase t, normFactor a t q z
      else (2:R)^(a+1-padicValInt 2 (t-k))*z *
        ∏ q ∈ ((grid a).erase t).erase k, normFactor a t q z := by
  have hc : (oddDerivative a:R)*oddInverse p (oddDerivative a:R)=1 :=
    inverse_int p hp _ (oddDerivative_odd a)
  unfold modular
  split <;> rw [mul_left_comm, hc, mul_one]

#print axioms factor_exact
#print axioms derivative_factored
#print axioms actual_normalized_same
#print axioms actual_normalized_other
#print axioms modular_denominator

end AOracleSuccinctKernel

