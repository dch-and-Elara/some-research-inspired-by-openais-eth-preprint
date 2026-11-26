import J6DeformationPoly

namespace J6DeformationOrigin
open scoped Classical BigOperators Polynomial
open P1DyadicGrid Polynomial J6DeformationPoly

variable {R P : Type*} [CommRing R] [Algebra ℚ R] [Fintype P]

omit [Fintype P] in
theorem entry_eval_int (a : ℕ) (k t : ℤ) :
    (entry R a k).eval (t:R) =
      algebraMap ℚ R (J6NativeHeightKernel.kernel a k t) := by
  unfold entry J6NativeHeightKernel.kernel
  rw [eval_mul, eval_C, div_eq_mul_inv, map_mul, mul_comm]
  congr 1
  simp [eval_prod, eval_sub, map_prod, Int.cast_sub]

omit [Fintype P] in
theorem entry_origin (a : ℕ) (k : ℤ) :
    (entry R a k).eval 0 = if k=0 then 1 else 0 := by
  rw [← Int.cast_zero (R:=R), entry_eval_int, J6NativeHeightKernel.kernel_at_node a k 0 (zero_mem_grid a)]
  by_cases h : k=0
  · have hd : (((cauchyPolynomial a).derivative.eval 0 : ℤ) : ℚ) ≠ 0 := by
      exact_mod_cast cauchy_derivative_nonzero (zero_mem_grid a)
    simp [h, P1DyadicGridBridge.derivRatio, div_self hd]
  · simp [h]

omit [Fintype P] in
theorem matrix_origin {K : Type*} [DecidableEq K]
    (page : P → K) (slot : P → ℤ) (a : ℕ)
    (hinj : Function.Injective (fun i => (page i,slot i))) (i j : P) :
    (matrix (R:=R) page slot a i j).eval 0 = if i=j then 1 else 0 := by
  classical
  by_cases h : i=j
  · subst j
    simp [matrix,entry_origin]
  · by_cases hp : page i = page j
    · have hn : slot j - slot i ≠ 0 := by
        intro e
        exact h (hinj (Prod.ext hp (sub_eq_zero.mp e).symm))
      simp [matrix,hp,entry_origin,hn,h]
    · simp [matrix,hp,h]

#print axioms entry_eval_int
#print axioms entry_origin
#print axioms matrix_origin
end J6DeformationOrigin
