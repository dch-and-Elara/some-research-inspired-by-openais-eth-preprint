import P5MainBalanceHermite

/-! Retained V coefficients of the literal bivariate main polynomial.
Center the outer (deformation) variable while leaving V untouched. -/
namespace P5MainBalance
open Polynomial
open scoped BigOperators Classical

abbrev Bivariate := Polynomial (Polynomial ℚ)

noncomputable def vSlice (s : ℕ) (p : Bivariate) : ℚ[X] :=
  Polynomial.ofFinsupp (p.toFinsupp.mapRange (fun b => b.coeff s) (by simp))

@[simp] theorem coeff_vSlice (s : ℕ) (p : Bivariate) (i : ℕ) :
    (vSlice s p).coeff i=(p.coeff i).coeff s := by
  rw [←Polynomial.toFinsupp_apply]
  simp [vSlice,Polynomial.toFinsupp_apply]

theorem vSlice_add (s : ℕ) (p q : Bivariate) : vSlice s (p+q)=vSlice s p+vSlice s q := by
  ext i
  simp

theorem vSlice_monomial (s k : ℕ) (b : ℚ[X]) :
    vSlice s (Polynomial.monomial k b)=Polynomial.monomial k (b.coeff s) := by
  ext i
  by_cases h : k=i <;> simp [Polynomial.coeff_monomial,h]

theorem vSlice_degree_lt (s : ℕ) (p : Bivariate) (k : ℕ) (h : p.degree<k) :
    (vSlice s p).degree<k := by
  rw [degree_lt_iff_coeff_zero] at h ⊢
  intro n hn
  simp [h n hn]

noncomputable def centerBivar (t : ℚ) (p : Bivariate) : Bivariate := p.comp (X+C (C t))

set_option maxHeartbeats 5400000 in
theorem vSlice_center (s : ℕ) (p : Bivariate) (t : ℚ) :
    vSlice s (centerBivar t p)=center t (vSlice s p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    unfold centerBivar at hp hq ⊢
    rw [add_comp,vSlice_add,hp,hq,vSlice_add,map_add]
  | monomial n b =>
    have hLift : (X+C t:ℚ[X]).map (C : ℚ→+*ℚ[X]) = (X+C (C t):Bivariate) := by simp
    unfold centerBivar
    rw [vSlice_monomial]
    change vSlice s ((monomial n b).comp (X+C (C t)))=(monomial n (b.coeff s)).comp (X+C t)
    rw [monomial_comp,monomial_comp,←hLift,←Polynomial.map_pow]
    ext i
    rw [coeff_vSlice,coeff_C_mul,coeff_map,coeff_C_mul,coeff_mul_C,mul_comm]

noncomputable def nativeCoeff (p : Bivariate) (t : ℚ) (j s : ℕ) : ℚ :=
  ((centerBivar t p).coeff j).coeff s

theorem native_coeff_slice (s j : ℕ) (p : Bivariate) (t : ℚ) :
    nativeCoeff p t j s = (center t (vSlice s p)).coeff j := by
  rw [←vSlice_center,coeff_vSlice]
  rfl

noncomputable def retainedOrigin (ell : ℕ) (p : Bivariate) : ℚ :=
  ∑ s : Fin ell,(p.coeff 0).coeff s

variable {I : Type*} [Fintype I]

/-- One common Hermite weight vector supplies the source terminal readout
at the origin, over all retained V-precisions and every input sign word. -/
theorem native_retained_hermite (t : I→ℚ) (ht : Function.Injective t) (j : I→ℕ) (ell : ℕ) :
    ∃ w : JetIndex j→ℚ, ∀ p : Bivariate, p.degree<↑(∑ i,j i) →
      retainedOrigin ell p=∑ a : JetIndex j × Fin ell,w a.1*nativeCoeff p (t a.1.1) a.1.2 a.2 := by
  obtain ⟨w,hw⟩ := actual_hermite_weights t ht j
  refine ⟨w,?_⟩
  intro p hp
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  unfold retainedOrigin
  apply Finset.sum_congr rfl
  intro s _
  calc
    _ = (vSlice s p).eval 0 := by rw [←coeff_zero_eq_eval_zero,coeff_vSlice]
    _ = ∑ a,w a*(center (t a.1) (vSlice s p)).coeff a.2 :=
      hw _ (vSlice_degree_lt s p _ hp)
    _ = _ := by simp only [native_coeff_slice]

theorem direct_retained_origin (p : ℚ[X]) :
    retainedOrigin 1 (p.map (C : ℚ→+*ℚ[X]))=p.eval 0 := by
  unfold retainedOrigin
  simp [coeff_zero_eq_eval_zero]

#print axioms coeff_vSlice
#print axioms vSlice_degree_lt
#print axioms vSlice_center
#print axioms native_coeff_slice
#print axioms native_retained_hermite
#print axioms direct_retained_origin
end P5MainBalance
