import P5HermiteTransportGenericCRT

/-! Actual E_t and D_t. The forward target scale and its inverse
are used literally, and D_t applies the inverse scaled CRT to a
node-supported coefficient vector before target truncation. -/
namespace Paper5.HermiteGeneric
open Polynomial Matrix
open scoped BigOperators Polynomial Classical

variable {K T : Type*} [Field K]

structure Layout (K T : Type*) [Field K] where
  center : T→K
  order : T→ℕ
  scale : T→K
  distinct : Function.Injective center
  nonzeroScale : ∀t,scale t≠0
  anchor : K
  anchorScale : K
  nonzeroAnchorScale : anchorScale≠0

noncomputable def pullback (a β : K) : K[X]→+*K[X] :=
  affinePolynomial (-(a*β⁻¹)) β⁻¹

noncomputable def backMonomial (a β : K) (j : ℕ) : K[X] := pullback a β (X^j)

theorem affine_cancels_pullback (a β : K) (hβ : β≠0) (p : K[X]) :
    affinePolynomial a β (pullback a β p)=p := by
  have h : (affinePolynomial a β).comp (pullback a β) = RingHom.id K[X] := by
    apply Polynomial.ringHom_ext
    · intro c
      change affinePolynomial a β (affinePolynomial (-(a*β⁻¹)) β⁻¹ (C c))=C c
      rw [affine_C,affine_C]
    · change affinePolynomial a β (affinePolynomial (-(a*β⁻¹)) β⁻¹ X)=X
      rw [affine_X,map_add,map_mul,affine_C,affine_C,affine_X,mul_add,
        ←map_mul,←mul_assoc,←map_mul,inv_mul_cancel₀ hβ,map_one,one_mul,mul_comm β⁻¹ a]
      simp
  exact RingHom.congr_fun h p

theorem backMonomial_natDegree (a β : K) (j : ℕ) : (backMonomial a β j).natDegree≤j := by
  rw [backMonomial,map_pow]
  have h : (pullback a β (X:K[X])).natDegree≤1 := by
    rw [pullback,affine_X]
    apply natDegree_add_le_of_degree_le
    · rw [Polynomial.natDegree_C]; decide
    · calc
        (C β⁻¹ * (X:K[X])).natDegree ≤ (C β⁻¹).natDegree + (X:K[X]).natDegree := natDegree_mul_le
        _ = 1 := by rw [Polynomial.natDegree_C,Polynomial.natDegree_X,zero_add]
  exact (natDegree_pow_le_of_le j h).trans_eq (Nat.mul_one _)

theorem product_backward_window (p : K[X]) {b d : ℕ} (hd : p.natDegree≤d)
    (a β : K) (j : Fin b) :
    (p*backMonomial a β j.val).degree < (↑(d+b):WithBot ℕ) := by
  by_cases h : p*backMonomial a β j.val=0
  · rw [h,degree_zero]
    exact WithBot.bot_lt_coe _
  · apply (natDegree_lt_iff_degree_lt h).1
    apply natDegree_mul_le.trans_lt
    exact (Nat.add_le_add hd (backMonomial_natDegree a β j)).trans_lt (Nat.add_lt_add_left j.isLt d)

noncomputable def inputMatrix (L : Layout K T) (b : ℕ) (t : T) :
    Matrix (Fin (L.order t)) (Fin b) K :=
  Matrix.of fun i j=> scalarObserve (L.center t) (L.scale t) (L.order t)
    (backMonomial L.anchor L.anchorScale j.val) i

theorem inputMatrix_represents (L : Layout K T) (b : ℕ) (t : T) (x : Fin b→K) :
    inputMatrix L b t *ᵥ x =
      scalarObserve (L.center t) (L.scale t) (L.order t) (pullback L.anchor L.anchorScale (polyOfCoeffs b x)) := by
  funext i
  rw [polyOfCoeffs_sum,map_sum,map_sum,Finset.sum_apply]
  change (∑ j : Fin b, inputMatrix L b t i j*x j)=_
  apply Finset.sum_congr rfl
  intro j _
  have he : pullback L.anchor L.anchorScale (C (x j)*X^j.val) =
      x j • backMonomial L.anchor L.anchorScale j.val := by
    rw [map_mul,backMonomial,pullback,affine_C,smul_eq_C_mul]
  rw [he,map_smul,Pi.smul_apply,smul_eq_mul,mul_comm]
  rfl

variable [Fintype T]

noncomputable def decode (L : Layout K T) (b : ℕ) :
    ((t : T)→Fin (L.order t)→K) →ₗ[K] (Fin b→K) :=
  (scalarObserve L.anchor L.anchorScale b).comp
    ((degreeLT K (∑t,L.order t)).subtype.comp
      (scaledHermite L.center L.distinct L.order L.scale L.nonzeroScale).symm.toLinearMap)

theorem actual_decode (L : Layout K T) (b : ℕ) (p : K[X])
    (h : p.degree < (↑(∑ t,L.order t):WithBot ℕ)) :
    decode L b (fun t=>scalarObserve (L.center t) (L.scale t) (L.order t) p) =
      scalarObserve L.anchor L.anchorScale b p := by
  let x : degreeLT K (∑t,L.order t) := ⟨p,mem_degreeLT.mpr h⟩
  let F := scaledHermite L.center L.distinct L.order L.scale L.nonzeroScale
  have he : F x = fun t=>scalarObserve (L.center t) (L.scale t) (L.order t) p :=
    funext (scaledHermite_apply L.center L.distinct L.order L.scale L.nonzeroScale x)
  rw [←he]
  change scalarObserve L.anchor L.anchorScale b ((F.symm (F x)).val)=_
  rw [LinearEquiv.symm_apply_apply]

variable [DecidableEq T]

noncomputable def decodeMatrix (L : Layout K T) (b : ℕ) (t : T) :
    Matrix (Fin b) (Fin (L.order t)) K :=
  Matrix.of fun i j=> decode L b (Pi.single t (Pi.single j 1)) i

theorem decode_sum (L : Layout K T) (b : ℕ) (y : (t : T)→Fin (L.order t)→K) (i : Fin b) :
    decode L b y i = ∑ t, (decodeMatrix L b t *ᵥ y t) i := by
  have he : (∑ t,Pi.single t (y t))=y := LinearMap.sum_single_apply (fun t : T=>Fin (L.order t)→K) y
  calc
    _ = ∑ t,decode L b (Pi.single t (y t)) i := by
      conv_lhs => rw [←he]
      rw [map_sum,Finset.sum_apply]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t _
      have hy : (∑ j : Fin (L.order t), y t j • (Pi.single j (1:K) : Fin (L.order t)→K))=y t := by
        calc
          _ = ∑ j,Pi.single j (y t j) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [←Pi.single_smul',smul_eq_mul,mul_one]
          _ = _ := Finset.univ_sum_single _
      let E := LinearMap.single K (fun s=>Fin (L.order s)→K) t
      change decode L b (E (y t)) i=_
      conv_lhs => rw [←hy]
      rw [map_sum,map_sum,Finset.sum_apply]
      simp only [Matrix.mulVec,dotProduct]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul,map_smul,Pi.smul_apply,smul_eq_mul,mul_comm]
      rfl

#print axioms affine_cancels_pullback
#print axioms backMonomial_natDegree
#print axioms product_backward_window
#print axioms inputMatrix_represents
#print axioms actual_decode
#print axioms decode_sum
end Paper5.HermiteGeneric
