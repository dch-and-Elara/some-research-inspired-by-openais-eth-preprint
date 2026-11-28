import J9FactorBounds
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative

namespace J9FactorBounds
open scoped BigOperators

section Mesh

open Polynomial

/-- Source Cauchy grid polynomial, enumerated by real root indices i−L. -/
noncomputable def nativeMesh (L : ℕ) : ℤ[X] :=
  ∏ i ∈ Finset.range (2*L), (X - C ((i:ℤ)-(L:ℤ)))

def meshSlope (N r : ℕ) : ℤ :=
  ∏ i ∈ (Finset.range N).erase r, ((r:ℤ) - (i:ℤ))

theorem nativeMesh_derivative_at_index (L r : ℕ) (hr : r < 2*L) :
    (nativeMesh L).derivative.eval ((r:ℤ)-(L:ℤ)) = meshSlope (2*L) r := by
  let f := fun i : ℕ => (X:ℤ[X]) - C ((i:ℤ)-(L:ℤ))
  let C0 := (r:ℤ)-(L:ℤ)
  let q := ∏ i ∈ (Finset.range (2*L)).erase r, f i
  have hp : nativeMesh L = (X-C C0)*q := by
    have hx := Finset.prod_erase_mul (Finset.range (2*L)) f (Finset.mem_range.mpr hr)
    change q * (X-C C0) = nativeMesh L at hx
    rw [← hx, mul_comm]
  rw [hp, derivative_mul, eval_add, eval_mul, eval_mul, derivative_X_sub_C]
  simp only [eval_one, one_mul, eval_sub, eval_X, eval_C, show (r:ℤ)-(L:ℤ) = C0 from rfl,
    sub_self, zero_mul, add_zero]
  dsimp [q,meshSlope]
  rw [eval_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp [f,C0]

theorem meshSlope_factorial (N r : ℕ) (hr : r < N) :
    meshSlope N r =
      (r.factorial:ℤ) * ((-1:ℤ)^(N-r-1) * ((N-r-1).factorial:ℤ)) := by
  let f (i : ℕ) := if i = r then (1:ℤ) else (r:ℤ)-(i:ℤ)
  let k := N-r-1
  have hN : N = (r+1)+k := by dsimp [k]; omega
  have he : meshSlope N r = ∏ i ∈ Finset.range N, f i := by
    have hh := Finset.prod_erase_mul (Finset.range N) f (Finset.mem_range.mpr hr)
    have hfr : f r = 1 := by simp [f]
    rw [hfr, mul_one] at hh
    rw [← hh]
    unfold meshSlope
    apply Finset.prod_congr rfl
    intro i hi
    simp [f, (Finset.mem_erase.mp hi).1]
  have hleft : (∏ i ∈ Finset.range (r+1), f i) = (r.factorial:ℤ) := by
    rw [Finset.prod_range_succ, show f r=1 by simp [f], mul_one]
    calc
      (∏ i ∈ Finset.range r, f i) = ∏ i ∈ Finset.range r, ((r-i:ℕ):ℤ) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hil := Finset.mem_range.mp hi
        simp [f, (ne_of_lt hil), Nat.cast_sub hil.le]
      _ = ((∏ i ∈ Finset.range r, (r-i):ℕ):ℤ) := by norm_cast
      _ = ((r.descFactorial r):ℤ) := by rw [Nat.descFactorial_eq_prod_range]
      _ = _ := by rw [Nat.descFactorial_self]
  have hright : (∏ i ∈ Finset.range k, f (r+1+i)) = (-1:ℤ)^k*(k.factorial:ℤ) := by
    calc
      _ = ∏ i ∈ Finset.range k, (-1:ℤ)*((i+1:ℕ):ℤ) := by
        apply Finset.prod_congr rfl
        intro i _
        have hh : r+1+i ≠ r := by omega
        simp [f,hh]
        ring
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
        congr 1
        exact_mod_cast Finset.prod_range_add_one_eq_factorial k
  rw [he, hN, Finset.prod_range_add, hleft, hright]
  rw [show r+1+k-r-1 = k by omega]

/-- The scalar used by the numeric certificate is not a free bounded input:
it is exactly the ratio of the original two formal grid derivatives. -/
theorem kernel_is_literal_grid_ratio (L : ℕ) (hL : 1 ≤ L) (hEven : L % 2 = 0) :
    (kernel L : ℚ) =
      (((nativeMesh L).derivative.eval ((L:ℤ)-1) : ℤ) : ℚ) /
        (((nativeMesh L).derivative.eval (0:ℤ) : ℤ) : ℚ) := by
  have h1 : L < 2*L := by omega
  have h2 : 2*L-1 < 2*L := by omega
  have ht : ((2*L-1:ℕ):ℤ)-(L:ℤ) = (L:ℤ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 2*L)]
    push_cast
    ring
  have hzero : (nativeMesh L).derivative.eval (0:ℤ) =
      -(L.factorial:ℤ)*((L-1).factorial:ℤ) := by
    have hx := nativeMesh_derivative_at_index L L h1
    rw [sub_self, meshSlope_factorial _ _ h1] at hx
    have hs : 2*L-L-1=L-1 := by omega
    have ho : Odd (L-1) := ⟨(L-1)/2, by omega⟩
    rw [hs, ho.neg_one_pow] at hx
    linarith only [hx]
  have htop : (nativeMesh L).derivative.eval ((L:ℤ)-1) = ((2*L-1).factorial:ℤ) := by
    have hx := nativeMesh_derivative_at_index L (2*L-1) h2
    rw [ht, meshSlope_factorial _ _ h2] at hx
    have hs : 2*L-(2*L-1)-1=0 := by omega
    simpa [hs] using hx
  have hz : (-(L.factorial:ℚ))*((L-1).factorial:ℚ) ≠ 0 := by
    apply mul_ne_zero
    · exact neg_ne_zero.mpr (by exact_mod_cast Nat.factorial_ne_zero L)
    · exact_mod_cast Nat.factorial_ne_zero (L-1)
  rw [hzero, htop]
  push_cast
  apply (eq_div_iff hz).2
  have hadd : (L-1)+L=2*L-1 := by omega
  have hh := Nat.add_choose_mul_factorial_mul_factorial (L-1) L
  rw [hadd] at hh
  have hx : (((2*L-1).choose L:ℕ):ℚ) * ((L-1).factorial:ℚ) *
      (L.factorial:ℚ) = ((2*L-1).factorial:ℚ) := by exact_mod_cast hh
  unfold kernel
  push_cast
  rw [← hx]
  ring

end Mesh

#print axioms nativeMesh_derivative_at_index
#print axioms meshSlope_factorial
#print axioms kernel_is_literal_grid_ratio
end J9FactorBounds

