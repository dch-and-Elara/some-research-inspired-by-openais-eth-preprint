import P5MainBalanceNative
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Sum

/-! The original signed interpolation polynomial is the printed
falling-factorial sum, not an arbitrary interpolation coefficient
vector. Its values on every retained interval weight are proved. -/
namespace P5MainBalance.M6
open Polynomial
open scoped BigOperators Classical

noncomputable def falling (a j : ℕ) : ℚ[X] :=
  C ((j.factorial:ℚ)⁻¹)*∏ u∈Finset.range j,(X-C ((a+u:ℕ):ℚ))

theorem falling_eval_natural (a j q : ℕ) :
    (falling a j).eval ((a+q:ℕ):ℚ)=(q.choose j:ℚ) := by
  have he (u : ℕ) : ((a+q:ℕ):ℚ)-((a+u:ℕ):ℚ)=(q:ℚ)-(u:ℚ) := by push_cast; ring
  unfold falling
  simp only [eval_mul,eval_C,eval_prod,eval_sub,eval_X,he]
  by_cases h : j≤q
  · have hp :=
      Finset.prod_congr (rfl : Finset.range j=Finset.range j) (fun u hu =>
        (Nat.cast_sub (show u≤q by have := Finset.mem_range.mp hu; omega) (R:=ℚ)).symm)
    rw [hp,←Nat.cast_prod,←Nat.descFactorial_eq_prod_range,Nat.descFactorial_eq_factorial_mul_choose,
      Nat.cast_mul,←mul_assoc,inv_mul_cancel₀ (by exact_mod_cast (Nat.factorial_ne_zero j)),one_mul]
  · have hz : (∏ u∈Finset.range j,((q:ℚ)-(u:ℚ)))=0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr (by omega) : q∈Finset.range j) (sub_self _)
    rw [hz,mul_zero,Nat.choose_eq_zero_of_lt (by omega)]
    rfl

noncomputable def printedInterval (A R : ℕ) : ℚ[X] :=
  C ((-1:ℚ)^A)*∑ j∈Finset.range R,C ((-2:ℚ)^j)*falling A j

theorem eval_printed_interval (A R q : ℕ) (hq : q<R) :
    (printedInterval A R).eval ((A+q:ℕ):ℚ)=(-1:ℚ)^(A+q) := by
  unfold printedInterval
  simp only [eval_mul,eval_C,eval_finset_sum,falling_eval_natural,pow_add]
  congr 1
  have h : Finset.range (q+1)⊆Finset.range R := Finset.range_mono (by omega)
  rw [←Finset.sum_subset h (fun j hj hn => by
    rw [Nat.choose_eq_zero_of_lt (by have := Finset.mem_range.not.mp hn; omega)]
    simp)]
  have hbinom := add_pow (-2:ℚ) 1 q
  simpa only [show ((-2:ℚ)+1)=-1 by norm_num,one_pow,mul_one] using hbinom.symm

theorem interval_eval_in_span (A R q : ℕ) (ha : A≤q) (hr : q<A+R) :
    (printedInterval A R).eval (q:ℚ)=(-1:ℚ)^q := by
  have hq : A+(q-A)=q := by omega
  simpa only [hq] using eval_printed_interval A R (q-A) (by omega)

#print axioms falling_eval_natural
#print axioms eval_printed_interval
#print axioms interval_eval_in_span
end P5MainBalance.M6
