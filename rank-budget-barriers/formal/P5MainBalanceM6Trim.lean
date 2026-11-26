import P5MainBalanceNative
import Mathlib.Algebra.Polynomial.BigOperators

/-! The source sparse computation truncates in V before invoking the
T-degree budget. Its raw polynomial lift need not satisfy that budget.
This section trims exactly the retained V range and proves all the
native Hasse coefficients and terminal values are unchanged. -/
namespace P5MainBalance.M6
open P5MainBalance Polynomial
open scoped BigOperators Classical

noncomputable def trimVOne (ell : ℕ) (p : ℚ[X]) : ℚ[X] :=
  ∑ s : Fin ell,monomial s.val (p.coeff s)

theorem trimVOne_coeff (ell s : ℕ) (p : ℚ[X]) :
    (trimVOne ell p).coeff s = if s<ell then p.coeff s else 0 := by
  unfold trimVOne
  rw [finset_sum_coeff]
  simp_rw [coeff_monomial]
  by_cases h : s<ell
  · rw [if_pos h,Finset.sum_eq_single (⟨s,h⟩:Fin ell)]
    · simp
    · intro q _ hq
      rw [if_neg (fun he=>hq (Fin.ext he))]
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro q _
    exact if_neg (fun he : q.val=s=>h (he ▸ q.isLt))

theorem trimVOne_zero (ell : ℕ) : trimVOne ell 0=0 := by simp [trimVOne]

noncomputable def trimV (ell : ℕ) (p : Bivariate) : Bivariate :=
  p.sum fun n c => monomial n (trimVOne ell c)

theorem trimV_coeff (ell j : ℕ) (p : Bivariate) :
    (trimV ell p).coeff j=trimVOne ell (p.coeff j) := by
  unfold trimV
  rw [Polynomial.sum_def,finset_sum_coeff]
  by_cases h : j∈p.support
  · rw [Finset.sum_eq_single_of_mem j h]
    · exact coeff_monomial_same _ _
    · intro n _ hn
      exact coeff_monomial_of_ne _ (Ne.symm hn)
  · rw [notMem_support_iff.mp h,trimVOne_zero]
    exact Finset.sum_eq_zero fun n hn=>coeff_monomial_of_ne _ (fun he=>h (he ▸ hn))

theorem vSlice_trim (ell s : ℕ) (hs : s<ell) (p : Bivariate) :
    vSlice s (trimV ell p)=vSlice s p := by
  ext j
  simp only [coeff_vSlice,trimV_coeff,trimVOne_coeff,if_pos hs]

theorem native_coeff_trim (ell : ℕ) (s : Fin ell) (p : Bivariate) (t : ℚ) (j : ℕ) :
    nativeCoeff (trimV ell p) t j s=nativeCoeff p t j s := by
  rw [native_coeff_slice,native_coeff_slice,vSlice_trim ell s.val s.isLt]

theorem retained_origin_trim (ell : ℕ) (p : Bivariate) :
    retainedOrigin ell (trimV ell p)=retainedOrigin ell p := by
  unfold retainedOrigin
  apply Finset.sum_congr rfl
  intro s _
  rw [trimV_coeff,trimVOne_coeff,if_pos s.isLt]

theorem trimmed_degree_iff (ell D : ℕ) (p : Bivariate) :
    (trimV ell p).degree<↑D ↔ ∀ s : Fin ell,(vSlice s p).degree<↑D := by
  constructor
  · intro h s
    rw [←vSlice_trim ell s.val s.isLt]
    exact vSlice_degree_lt _ _ _ h
  · intro h
    rw [degree_lt_iff_coeff_zero]
    intro d hd
    rw [trimV_coeff]
    ext s
    rw [trimVOne_coeff,coeff_zero]
    split
    · rename_i hs
      have hh := h ⟨s,hs⟩
      rw [degree_lt_iff_coeff_zero] at hh
      exact (coeff_vSlice s (p:=p) d).symm.trans (hh d hd)
    · rfl

#print axioms trimVOne_coeff
#print axioms trimV_coeff
#print axioms native_coeff_trim
#print axioms retained_origin_trim
#print axioms trimmed_degree_iff
end P5MainBalance.M6
