import V8NativeMessageC3MainList

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3300000

/-! Actual MAIN row and private arguments have the designated common
integer denominator after the source substitution, including the
negative-centre subtraction in the Taylor correction. -/
namespace V8NativeMessage.C3.RawMain
open scoped Classical BigOperators Polynomial
open Polynomial V8PooledRange
noncomputable section

def intPolynomialImage : Subring ℚ[X] :=
  (mapRingHom (Int.castRingHom ℚ)).range

theorem integer_coeffs_lift (q : ℚ[X]) (h : ∀ n, ∃ a : ℤ, (a:ℚ)=q.coeff n) :
    q∈intPolynomialImage := by
  choose a ha using h
  refine ⟨∑ n∈q.support, monomial n (a n),?_⟩
  change (∑ n∈q.support, monomial n (a n)).map (Int.castRingHom ℚ) = q
  simp only [Polynomial.map_sum,Polynomial.map_monomial]
  calc
    _ = ∑ n∈q.support, monomial n (q.coeff n) :=
      Finset.sum_congr rfl (fun n _ => congrArg (monomial n) (ha n))
    _ = q := q.as_sum_support.symm

theorem C_integer (n : ℤ) : C (n:ℚ)∈intPolynomialImage :=
  ⟨C n,by simp⟩

theorem shift_integral (n : ℤ) : (C (n:ℚ)+X)∈intPolynomialImage :=
  ⟨C n+X,by simp⟩

theorem comp_integer {p q : ℚ[X]} (hp : p∈intPolynomialImage) (hq : q∈intPolynomialImage) :
    p.comp q∈intPolynomialImage := by
  obtain ⟨u,rfl⟩ := hp
  obtain ⟨v,rfl⟩ := hq
  refine ⟨u.comp v,?_⟩
  exact Polynomial.map_comp _ _ _

theorem C_eval_integer {p : ℚ[X]} (hp : p∈intPolynomialImage) (n : ℤ) :
    C (p.eval (n:ℚ))∈intPolynomialImage := by
  obtain ⟨u,rfl⟩ := hp
  have he : ((u.map (Int.castRingHom ℚ)).eval (n:ℚ))=((u.eval n:ℤ):ℚ) := by
    rw [Polynomial.eval_map]
    exact Polynomial.eval₂_hom (Int.castRingHom ℚ) n
  change C (((u.map (Int.castRingHom ℚ)).eval (n:ℚ)))∈intPolynomialImage
  rw [he]
  exact C_integer _

variable {V E Γ : Type} [Fintype V] [Fintype E] [Fintype Γ] (L : Layout V E Γ)

def δ : ℕ := (L.R-1).factorial*L.Q.factorial

theorem scaled_row_integral (f : ClauseId V E) (v : Variable V) (hv : v∈L.scope f)
    (w : Variable V) :
    C (δ L : ℚ) * L.replacement f v w∈intPolynomialImage := by
  apply integer_coeffs_lift
  intro j
  obtain ⟨a,ha⟩ := L.scaled_integral f v hv w j
  refine ⟨a,?_⟩
  simpa only [δ,coeff_C_mul] using ha.symm

theorem scaled_base_integral (a : Address L) (g : Γ) (x : Fibre L a g)
    (f : ClauseId V E) (v : Variable V) (hv : v∈L.scope f) :
    C (δ L:ℚ)*C (base L a g x f v)∈intPolynomialImage := by
  rw [← C_mul,base,Finset.mul_sum,map_sum]
  apply Subring.sum_mem
  intro w _
  have hshow : ((C (δ L:ℚ)*L.replacement f v w).eval (positiveNode a.t:ℚ)) =
      (δ L:ℚ)*(L.replacement f v w).eval (positiveNode a.t:ℚ) := by simp
  by_cases h : replacementWord L a g x w=true
  · simp only [if_pos h,mul_one]
    rw [← hshow]
    exact C_eval_integer (scaled_row_integral L f v hv w) (positiveNode a.t : ℤ)
  · simp only [if_neg h,mul_zero,map_zero]
    exact Subring.zero_mem _

theorem actual_theta_denominator (a : Address L) (g : Γ) (x : Fibre L a g)
    (f : ClauseId V E) (v : Variable V) (hv : v∈L.scope f) :
    C (δ L:ℚ)*thetaPolynomial L a g x f v∈intPolynomialImage := by
  rw [thetaPolynomial,mul_add,Finset.mul_sum]
  refine Subring.add_mem _ (scaled_base_integral L a g x f v hv) ?_
  apply Subring.sum_mem
  intro w _
  rw [mul_sub]
  apply Subring.sub_mem
  · have hh : C (δ L:ℚ)*(L.replacement f v w).comp (C (positiveNode a.t:ℚ)+X) =
      (C (δ L:ℚ)*L.replacement f v w).comp (C (positiveNode a.t:ℚ)+X) := by simp [mul_comp]
    rw [hh]
    exact comp_integer (scaled_row_integral L f v hv w) (shift_integral (positiveNode a.t:ℤ))
  · have hh : C (δ L:ℚ)*C ((L.replacement f v w).eval (positiveNode a.t:ℚ)) =
        C ((C (δ L:ℚ)*L.replacement f v w).eval (positiveNode a.t:ℚ)) := by simp
    rw [hh]
    exact C_eval_integer (scaled_row_integral L f v hv w) (positiveNode a.t:ℤ)

#print axioms integer_coeffs_lift
#print axioms C_eval_integer
#print axioms scaled_row_integral
#print axioms scaled_base_integral
#print axioms actual_theta_denominator
end
end V8NativeMessage.C3.RawMain