import P5P3Unique
import P5P3ActualError
import P5P3Largest

/-! Full decoder interpretation on the degree-admissible editor window.
This separates the proof on exact data from robustness to independent
finite-precision coefficient errors. -/
namespace Paper5.P3
open scoped BigOperators Polynomial
open Polynomial

variable {K : Type*} [Field K] {T : Type*} [Fintype T] [DecidableEq T]

theorem exact_window_test (O : Subring K) (u : T→K) (q : T→ℕ) (d b : ℕ)
    (hb : degreeAdmissible q d b) (hi : Function.Injective u) (hd : ∀ r s,(u r-u s)⁻¹∈O)
    (A : K[X]) (hA : A.natDegree≤d) (j : Fin b) :
    fixedInterpolate O u q hd (fun t => shift (u t) A * shift (u t) (X^j.val)) = A*X^j.val := by
  obtain ⟨hb,hfit⟩ := hb
  have hs : 0<∑ t,q t := by omega
  have hd' : (A*X^j.val).natDegree < ∑ t,q t := by
    have h := Polynomial.natDegree_mul_le (p:=A) (q:=(X^j.val:K[X]))
    simp only [Polynomial.natDegree_X_pow] at h
    have hj := j.isLt
    omega
  refine unique_degree_interpolation u q hi _ _ (fixed_interpolate_degree O u q hs hd _) ?_ ?_
  · exact (Polynomial.degree_le_natDegree (p:=A*X^j.val)).trans_lt (WithBot.coe_lt_coe.mpr hd')
  · intro t
    rw [fixed_interpolate_jets O u q hi hd _ t]
    simp only [map_mul]

theorem fixed_interpolate_add (O : Subring K) (u : T→K) (q : T→ℕ)
    (hd : ∀ r s,(u r-u s)⁻¹∈O) (x y : T→K[X]) :
    fixedInterpolate O u q hd (fun t => x t+y t) =
      fixedInterpolate O u q hd x+fixedInterpolate O u q hd y := by
  simp only [fixedInterpolate,single_add,Finset.sum_add_distrib]

theorem coefficient_change_is_error (O : Subring K) (u : T→K) (q : T→ℕ)
    (hd : ∀ r s,(u r-u s)⁻¹∈O) (x y : T→K[X]) (i : ℕ) :
    (fixedInterpolate O u q hd (fun t => x t+y t)).coeff i -
        (fixedInterpolate O u q hd x).coeff i =
      (fixedInterpolate O u q hd y).coeff i := by
  rw [fixed_interpolate_add,coeff_add,add_sub_cancel_left]

#print axioms exact_window_test
#print axioms fixed_interpolate_add
#print axioms coefficient_change_is_error
end Paper5.P3
