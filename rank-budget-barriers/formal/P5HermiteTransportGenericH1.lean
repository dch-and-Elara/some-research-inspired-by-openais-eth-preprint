import P5HermiteTransportGenericProduct
import P5HermiteTransportGenericExpansion

/-! Paper 5 (H.1): actual scaled Hermite reconstruction, including
literal coefficient-first D_t/E_t, no desired-output receipt and no
rank assumption needed for the identity. -/
namespace Paper5.HermiteGeneric
open Polynomial Matrix
open scoped BigOperators Polynomial Kronecker Classical

variable {K T : Type*} [Field K] [Fintype T] [DecidableEq T]

omit [Fintype T] [DecidableEq T] in
theorem product_column_node (L : Layout K T) (b : ℕ) (p : K[X])
    (t : T) (i : Fin (L.order t)) (j : Fin b) :
    scalarObserve (L.center t) (L.scale t) (L.order t) (p*backMonomial L.anchor L.anchorScale j.val) i =
      (scalarConvolution (scalarObserve (L.center t) (L.scale t) (L.order t) p) *
        inputMatrix L b t) i j := by
  simpa only [Matrix.mul_apply,Matrix.mulVec,dotProduct] using
    affine_product_coeff (L.center t) (L.scale t) (L.order t) p
      (backMonomial L.anchor L.anchorScale j.val) i

omit [Fintype T] [DecidableEq T] in
theorem product_column_anchor (L : Layout K T) (b : ℕ) (p : K[X]) (i j : Fin b) :
    scalarObserve L.anchor L.anchorScale b (p*backMonomial L.anchor L.anchorScale j.val) i =
      scalarConvolution (scalarObserve L.anchor L.anchorScale b p) i j := by
  rw [scalarObserve_apply,map_mul,backMonomial,affine_cancels_pullback _ _ L.nonzeroAnchorScale,
    Polynomial.coeff_mul_X_pow',scalarConvolution_apply]
  by_cases h : j.val ≤ i.val
  · rw [if_pos h,dif_pos h]; rfl
  · rw [if_neg h,dif_neg h]

theorem scalar_reconstruct (L : Layout K T) (b d : ℕ) (p : K[X]) (hd : p.natDegree≤d)
    (hWindow : d+b≤∑t,L.order t) (i j : Fin b) :
    scalarConvolution (scalarObserve L.anchor L.anchorScale b p) i j =
      ∑ t,(decodeMatrix L b t *
        scalarConvolution (scalarObserve (L.center t) (L.scale t) (L.order t) p) *
        inputMatrix L b t) i j := by
  let q := p*backMonomial L.anchor L.anchorScale j.val
  have hw : q.degree < (↑(∑t,L.order t):WithBot ℕ) :=
    (product_backward_window p hd L.anchor L.anchorScale j).trans_le (WithBot.coe_le_coe.mpr hWindow)
  have h := congrFun (actual_decode L b q hw) i
  rw [decode_sum] at h
  calc
    _ = scalarObserve L.anchor L.anchorScale b q i := (product_column_anchor L b p i j).symm
    _ = ∑t,(decodeMatrix L b t *ᵥ scalarObserve (L.center t) (L.scale t) (L.order t) q) i := h.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      rw [Matrix.mul_assoc,Matrix.mul_apply,Matrix.mulVec,dotProduct]
      apply Finset.sum_congr rfl
      intro a _
      rw [show q=p*backMonomial L.anchor L.anchorScale j.val from rfl,product_column_node]

theorem scalar_reconstruct_expanded (L : Layout K T) (b d : ℕ) (p : K[X]) (hd : p.natDegree≤d)
    (hWindow : d+b≤∑t,L.order t) (i j : Fin b) :
    scalarConvolution (scalarObserve L.anchor L.anchorScale b p) i j =
      ∑ t,∑ a : Fin (L.order t),transfer L b t a i j*scalarObserve (L.center t) (L.scale t) (L.order t) p a := by
  rw [scalar_reconstruct L b d p hd hWindow]
  apply Finset.sum_congr rfl
  intro t _
  rw [scalarConvolution,Matrix.mul_sum,Matrix.sum_mul,Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [Matrix.mul_smul,Matrix.smul_mul,Matrix.smul_apply,smul_eq_mul,mul_comm]; rfl

set_option maxHeartbeats 9500000 in
theorem reconstruction_expanded {U V : Type*} (L : Layout K T) (b d : ℕ)
    (A : Matrix U V K[X]) (hDegree : ∀ u v,(A u v).natDegree≤d)
    (hWindow : d+b≤∑t,L.order t) :
    anchorMatrix L b A = expanded L b (nativeCoefficients L A) := by
  apply Matrix.ext
  rintro ⟨i,u⟩ ⟨j,v⟩
  have h := scalar_reconstruct_expanded L b d (A u v) (hDegree u v) hWindow i j
  unfold anchorMatrix expanded
  rw [convolution_apply]
  rw [scalarConvolution_apply] at h
  simp only [Matrix.sum_apply,Matrix.kronecker_apply]
  exact h

theorem reconstruction_H1 {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]
    (L : Layout K T) (b d : ℕ) (A : Matrix U V K[X])
    (hDegree : ∀ u v,(A u v).natDegree≤d) (hWindow : d+b≤∑t,L.order t) :
    anchorMatrix L b A = compressed L b (nativeCoefficients L A) ∧
    anchorMatrix L b A = expanded L b (nativeCoefficients L A) := by
  have h := reconstruction_expanded L b d A hDegree hWindow
  exact ⟨h.trans (compressed_eq_expanded L b (nativeCoefficients L A)).symm,h⟩

#print axioms product_column_node
#print axioms product_column_anchor
#print axioms scalar_reconstruct
#print axioms scalar_reconstruct_expanded
#print axioms reconstruction_expanded
#print axioms reconstruction_H1
end Paper5.HermiteGeneric
