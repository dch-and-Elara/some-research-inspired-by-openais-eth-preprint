import P5H4WidthLower

/-! The literal H.4–H.6 sharpness examples in §2.3, before making
any change from the jet quotient back to fraction-field rank. -/
namespace Paper5.HermiteExamples
open Polynomial Matrix
open scoped Polynomial Classical

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 7000000

noncomputable section
variable {K : Type*} [Field K]

abbrev twoJet (K : Type*) [Field K] := AdjoinRoot ((X-C (0:K))^2)

def twoJetDiagonal (K : Type*) [Field K] : Matrix (Fin 2) (Fin 2) (twoJet K) :=
  (Matrix.diagonal (fun _ : Fin 2 => (X:K[X]))).map (AdjoinRoot.mk ((X-C (0:K))^2))

theorem zero_jet_determinant_but_width_two :
    (twoJetDiagonal K).det=0 ∧
      (∀ w : ℕ, (∃ U : Matrix (Fin 2) (Fin w) (twoJet K),
        ∃ V : Matrix (Fin w) (Fin 2) (twoJet K), twoJetDiagonal K=U*V) → 2≤w) ∧
      (∃ U V : Matrix (Fin 2) (Fin 2) (twoJet K),twoJetDiagonal K=U*V) := by
  let q : K[X] := (X-C 0)^2
  have hq : (X:K[X])^2=q := by simp [q]
  refine ⟨?_,?_,⟨twoJetDiagonal K,1,by simp⟩⟩
  · unfold twoJetDiagonal
    change ((AdjoinRoot.mk q).mapMatrix (Matrix.diagonal (fun _ : Fin 2 => (X:K[X])))).det=0
    rw [←RingHom.map_det,Matrix.det_diagonal,Fin.prod_univ_two,←pow_two,hq]
    exact AdjoinRoot.mk_self
  · intro w h
    have hf := (P5H4.factors_iff_quotient (r:=Fin w) q
      (Matrix.diagonal (fun _ : Fin 2 => (X:K[X])))).mpr h
    have hroot : rootMultiplicity (0:K) X=1 := by
      simpa using (rootMultiplicity_X_sub_C_self (x:=(0:K)))
    have hc := P5H4.diagonal_width_lower (r:=Fin w) (fun _ : Fin 2 => (X:K[X]))
      (fun _=>X_ne_zero) (0:K) 2 hf
    simpa [hroot] using hc

def threeLinearDiagonal (K : Type*) [Field K] : Matrix (Fin 3) (Fin 3) K[X] :=
  (X:K[X]) • (1 : Matrix (Fin 3) (Fin 3) K[X])

theorem every_two_minor_vanishes_but_det_only_order_three :
    (∀ rows cols : Fin 2→Fin 3,
      (X : K[X])^2 ∣ ((threeLinearDiagonal K).submatrix rows cols).det) ∧
      rootMultiplicity (0:K) (threeLinearDiagonal K).det=3 ∧
      ¬(X:K[X])^4 ∣ (threeLinearDiagonal K).det := by
  have hdet : (threeLinearDiagonal K).det=(X:K[X])^3 := by
    simp [threeLinearDiagonal]
  have horder : rootMultiplicity (0:K) (threeLinearDiagonal K).det=3 := by
    rw [hdet]
    simpa using (rootMultiplicity_X_sub_C_pow (0:K) 3)
  refine ⟨?_,horder,?_⟩
  · intro rows cols
    have hM : (threeLinearDiagonal K).submatrix rows cols =
        (X:K[X]) • ((1 : Matrix (Fin 3) (Fin 3) K[X]).submatrix rows cols) := rfl
    rw [hM,Matrix.det_smul,Fintype.card_fin]
    exact dvd_mul_right _ _
  · intro h
    have hp : (threeLinearDiagonal K).det≠0 := hdet.symm ▸ pow_ne_zero 3 X_ne_zero
    have hm := (le_rootMultiplicity_iff hp).mpr
      (show (X-C (0:K))^4 ∣ (threeLinearDiagonal K).det by simpa using h)
    omega

#print axioms zero_jet_determinant_but_width_two
#print axioms every_two_minor_vanishes_but_det_only_order_three
end
end Paper5.HermiteExamples
