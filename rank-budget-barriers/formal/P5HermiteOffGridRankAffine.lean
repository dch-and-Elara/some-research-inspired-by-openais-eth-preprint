import P5HermiteTransportGenericExpansion

/-! The original E_t is surjective in the printed positive degree
window b >= k_t. Use the actual two inverse affine coordinates. -/
namespace Paper5.HermiteOffGrid
open Paper5.HermiteGeneric Polynomial Matrix
open scoped BigOperators Polynomial Classical

variable {K T : Type*} [Field K]

theorem affine_degree_le (a β : K) (p : K[X]) :
    (affinePolynomial a β p).natDegree≤p.natDegree := by
  change (p.comp (C a+C β*X)).natDegree≤p.natDegree
  have h : (C a+C β*(X:K[X])).natDegree≤1 := by
    apply natDegree_add_le_of_degree_le
    · rw [Polynomial.natDegree_C]; decide
    · calc
        _ ≤ (C β).natDegree+(X:K[X]).natDegree := natDegree_mul_le
        _ = _ := by rw [Polynomial.natDegree_C,Polynomial.natDegree_X,zero_add]
  exact natDegree_comp_le.trans ((Nat.mul_le_mul_left _ h).trans_eq (Nat.mul_one _))

theorem pullback_after_affine (a β : K) (hβ : β≠0) (p : K[X]) :
    pullback a β (affinePolynomial a β p)=p := by
  have h : - ((-(a*β⁻¹)) * (β⁻¹)⁻¹)=a := by
    rw [inv_inv,neg_mul,neg_neg,mul_assoc,inv_mul_cancel₀ hβ,mul_one]
  have he : pullback (-(a*β⁻¹)) β⁻¹=affinePolynomial a β := by
    unfold pullback
    rw [h,inv_inv]
  rw [←he]
  exact affine_cancels_pullback _ _ (inv_ne_zero hβ) p

theorem polyOfCoeffs_outside (b : ℕ) (x : Fin b→K) (i : ℕ) (hi : b ≤ i) :
    (polyOfCoeffs b x).coeff i=0 :=
  testVec_other_coeff b (fun j : Unit × Fin b=>x j.2) () i hi

theorem polyOfCoeffs_degree (b : ℕ) (x : Fin b→K) :
    (polyOfCoeffs b x).natDegree≤b-1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  exact polyOfCoeffs_outside b x i (by omega)

theorem polyOfCoeffs_recovers (b : ℕ) (p : K[X]) (hp : p.degree<(↑b:WithBot ℕ)) :
    polyOfCoeffs b (fun i=>p.coeff i.val)=p := by
  apply Polynomial.ext
  intro i
  by_cases hi : i<b
  · exact polyOfCoeffs_coeff b _ ⟨i,hi⟩
  · rw [polyOfCoeffs_outside b (fun j : Fin b=>p.coeff j.val) i (Nat.le_of_not_gt hi),
      coeff_eq_zero_of_degree_lt (hp.trans_le (WithBot.coe_le_coe.mpr (Nat.le_of_not_gt hi)))]

set_option maxHeartbeats 14000000 in
theorem actual_input_surjective (L : Layout K T) (b : ℕ) (t : T)
    (ht : 0<L.order t) (hB : L.order t≤b) :
    Function.Surjective (inputMatrix L b t).mulVecLin := by
  intro y
  let p := polyOfCoeffs (L.order t) y
  let q := pullback (L.center t) (L.scale t) p
  let h := affinePolynomial L.anchor L.anchorScale q
  have hd : h.natDegree≤L.order t-1 := by
    calc
      _ ≤ q.natDegree := affine_degree_le _ _ _
      _ ≤ p.natDegree := affine_degree_le _ _ _
      _ ≤ _ := polyOfCoeffs_degree _ _
  have hNd : h.natDegree < b := by omega
  have hD : h.degree<(↑b:WithBot ℕ) :=
    degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr hNd)
  refine ⟨fun i=>h.coeff i.val,?_⟩
  change inputMatrix L b t *ᵥ (fun i=>h.coeff i.val)=y
  rw [inputMatrix_represents,polyOfCoeffs_recovers b h hD]
  change scalarObserve (L.center t) (L.scale t) (L.order t)
    (pullback L.anchor L.anchorScale (affinePolynomial L.anchor L.anchorScale q))=y
  rw [pullback_after_affine _ _ L.nonzeroAnchorScale]
  funext i
  change (affinePolynomial (L.center t) (L.scale t)
    (pullback (L.center t) (L.scale t) p)).coeff i.val=y i
  rw [affine_cancels_pullback _ _ (L.nonzeroScale t)]
  exact polyOfCoeffs_coeff _ _ _

#print axioms affine_degree_le
#print axioms pullback_after_affine
#print axioms polyOfCoeffs_recovers
#print axioms actual_input_surjective
end Paper5.HermiteOffGrid
