
import S11GridValuation

noncomputable section
namespace S11
open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]
variable (v : AddValuation K (WithTop ℤ)) (h₂ : v (2:K) = 1)

def shiftScale (K : Type*) [Field K] (a : ℕ) : K := 2^(a+1)

include h₂ in
theorem val_two_pow (n : ℕ) : v ((2:K)^n) = ↑(n:ℤ) := by
  rw [v.map_pow,h₂,← WithTop.coe_one,← WithTop.coe_nsmul]
  simp

private theorem val_prod_int {I : Type*} (s : Finset I) (f : I → K) (g : I → ℤ)
    (hf : ∀ i ∈ s, v (f i) = ↑(g i)) : v (∏ i ∈ s, f i) = ↑(∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, v.map_mul, WithTop.coe_add,
      hf i (Finset.mem_insert_self _ _), ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

def denominatorVal (a : ℕ) : ℕ := ∑ q ∈ (grid (2^a)).erase 0, level q

include h₂ in
theorem val_origin_denominator (a : ℕ) :
    v (originDenominator K (2^a)) = ↑(denominatorVal a : ℤ) := by
  unfold originDenominator denominatorVal
  rw [Nat.cast_sum]
  apply val_prod_int v
  intro q hq
  rw [v.map_neg]
  exact S7.valuation_integer v h₂ q (Finset.mem_erase.1 hq).1

def shiftedFactor (K : Type*) [Field K] (a : ℕ) (t q : ℤ) : K[X] :=
  C (((t - q : ℤ) : K)) + C (shiftScale K a) * X

def factorVal (a : ℕ) (t q : ℤ) : ℕ := if q = t then a+1 else level (t-q)

include h₂ in
theorem shifted_factor_bound {a : ℕ} {t q : ℤ}
    (ht : t ∈ grid (2^a)) (hq : q ∈ grid (2^a)) :
    S7.CoeffBound v (↑(factorVal a t q : ℤ)) (shiftedFactor K a t q) := by
  unfold shiftedFactor shiftScale
  have hp : S7.CoeffBound v (↑((a+1:ℕ):ℤ)) (C ((2:K)^(a+1)) * X) := by
    simpa only [val_two_pow v h₂, add_zero] using
      S7.bound_mul v (S7.bound_C v ((2:K)^(a+1))) (S7.bound_X v)
  by_cases h : q = t
  · subst q
    simpa [factorVal] using hp
  have he : v (((t-q:ℤ):K)) = (↑(level (t-q):ℤ) : WithTop ℤ) :=
    S7.valuation_integer v h₂ _ (sub_ne_zero.2 (Ne.symm h))
  have hle : level (t-q) ≤ a := level_diff_bound ht hq (Ne.symm h)
  have hconst := S7.bound_C v (((t-q:ℤ):K))
  rw [he] at hconst
  have hh : (↑(level (t-q):ℤ) : WithTop ℤ) ≤ ↑((a+1:ℕ):ℤ) := by
    norm_cast
    omega
  simpa only [factorVal, if_neg h] using S7.bound_add v hconst (S7.bound_weaken v hh hp)

include h₂ in
private theorem shifted_prod_bound (a : ℕ) (t : ℤ) (ht : t ∈ grid (2^a))
    (s : Finset ℤ) (hs : s ⊆ grid (2^a)) :
    S7.CoeffBound v (↑((∑ q ∈ s, factorVal a t q : ℕ):ℤ))
      (∏ q ∈ s, shiftedFactor K a t q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using S7.bound_one (K := K) v
  | insert q s hq ih =>
    rw [Finset.sum_insert hq,Finset.prod_insert hq,Nat.cast_add,WithTop.coe_add]
    exact S7.bound_mul v (shifted_factor_bound v h₂ ht (hs (Finset.mem_insert_self _ _)))
      (ih (fun x hx => hs (Finset.mem_insert_of_mem hx)))

theorem sum_factorVal {a : ℕ} {t : ℤ} (ht : t ∈ grid (2^a)) :
    ∑ q ∈ grid (2^a), factorVal a t q = (a+1)+denominatorVal a := by
  rw [← Finset.sum_erase_add _ _ ht]
  have he : (∑ q ∈ (grid (2^a)).erase t, factorVal a t q) =
      ∑ q ∈ (grid (2^a)).erase t, level (t-q) := by
    apply Finset.sum_congr rfl
    intro q hq
    simp [factorVal, (Finset.mem_erase.1 hq).1]
  rw [he, valuation_multiset ht (fun k : ℕ => k)]
  simp [denominatorVal, factorVal, Nat.add_comm]

def shiftedNumerator (K : Type*) [Field K] (a : ℕ) (t : ℤ) : K[X] :=
  C (originDenominator K (2^a))⁻¹ * ∏ q ∈ grid (2^a), shiftedFactor K a t q

include h₂ in
theorem shifted_numerator_bound {a : ℕ} {t : ℤ} (ht : t ∈ grid (2^a)) :
    S7.CoeffBound v (↑((a+1:ℕ):ℤ)) (shiftedNumerator K a t) := by
  unfold shiftedNumerator
  have h := shifted_prod_bound v h₂ a t ht _ (Finset.Subset.refl _)
  rw [sum_factorVal ht] at h
  have hc := S7.bound_mul v (S7.bound_C v ((originDenominator K (2^a))⁻¹)) h
  rw [v.map_inv, val_origin_denominator v h₂, Nat.cast_add,
    ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add] at hc
  convert hc using 2
  ring

theorem shiftedKernel_eq {a : ℕ} (x y : Fin (2^a)) (t : ℤ) :
    (packetKernel K (2^a) x y).comp (C (t:K) + C (shiftScale K a)*X) =
      C (originDenominator K (2^a))⁻¹ *
        ∏ q ∈ (grid (2^a)).erase ((y:ℤ)-(x:ℤ)), shiftedFactor K a t q := by
  change compRingHom _ _ = _
  rw [packetKernel, map_mul, map_prod]
  simp only [coe_compRingHom, C_comp]
  apply congrArg (_ * ·)
  apply Finset.prod_congr rfl
  intro q _
  simp only [sub_comp, X_comp, C_comp, shiftedFactor, Int.cast_sub, C_sub]
  ring

include h₂ in
theorem kernel_integral_shift {a : ℕ} (x y : Fin (2^a)) {t : ℤ} (ht : t ∈ grid (2^a)) :
    S7.CoeffBound v 0 ((packetKernel K (2^a) x y).comp
      (C (t:K) + C (shiftScale K a)*X)) := by
  rw [shiftedKernel_eq]
  let b : ℤ := (y:ℤ)-(x:ℤ)
  have hb : b ∈ grid (2^a) := by
    rw [grid_bounds]
    have hx := x.isLt
    have hy := y.isLt
    have hp : ((2^a:ℕ):ℤ) = (2:ℤ)^a := by push_cast; rfl
    unfold b
    omega
  have hfab : factorVal a t b ≤ a+1 := by
    by_cases h : b = t
    · simp [factorVal,h]
    · simp [factorVal, h, (level_diff_bound ht hb (Ne.symm h)).trans (Nat.le_succ _)]
  have hsum := Finset.sum_erase_add (grid (2^a)) (factorVal a t) hb
  rw [sum_factorVal ht] at hsum
  have hge : denominatorVal a ≤ ∑ q ∈ (grid (2^a)).erase b, factorVal a t q := by omega
  have h := shifted_prod_bound v h₂ a t ht ((grid (2^a)).erase b) (Finset.erase_subset _ _)
  have hc := S7.bound_mul v (S7.bound_C v ((originDenominator K (2^a))⁻¹)) h
  rw [v.map_inv, val_origin_denominator v h₂, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add] at hc
  apply S7.bound_weaken v _ hc
  exact_mod_cast (show (0:ℤ) ≤ -(denominatorVal a : ℤ) +
    ((∑ q ∈ (grid (2^a)).erase b, factorVal a t q : ℕ):ℤ) by omega)

theorem eval_bound {f : K[X]} {c : WithTop ℤ} (hf : S7.CoeffBound v c f) {z : K}
    (hz : 0 ≤ v z) : c ≤ v (f.eval z) := by
  rw [eval_eq_sum_range]
  apply S7.valuation_sum_bound v
  intro j _
  rw [v.map_mul, v.map_pow]
  exact (hf j).trans (le_add_of_nonneg_right (nsmul_nonneg hz j))

#print axioms val_origin_denominator
#print axioms shifted_numerator_bound
#print axioms kernel_integral_shift
#print axioms eval_bound

end S11

