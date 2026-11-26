import P5A11FiniteLocal
import RBSharp

/-! The ordinary field-centered quotient and the source's affine
coefficient jet are isomorphic exactly at invertible scales. Thus the
field determinant budget applies to the mod-pi rank of the source map. -/
namespace Paper5
open scoped BigOperators Polynomial
open Polynomial Matrix

variable {K : Type*} [Field K]

theorem affine_field_jet_equiv (t a : K) (ha : a≠0) (k : ℕ) :
    ∃ e : RankBudget.Jet t k ≃ₐ[K] PlainJet K k, ∀ p : K[X],
      e (AdjoinRoot.mk ((X-C t)^k) p) = AdjoinRoot.mk (X^k) (affinePolynomial t a p) := by
  let U := RankBudget.Jet t k
  let V := PlainJet K k
  let u : U := AdjoinRoot.root ((X-C t)^k)
  let v : V := AdjoinRoot.root (X^k : K[X])
  have hu : (u - algebraMap K U t)^k = 0 := by
    change (AdjoinRoot.mk ((X-C t)^k) X - AdjoinRoot.mk ((X-C t)^k) (C t))^k=0
    rw [←map_sub,←map_pow,AdjoinRoot.mk_self]
  have hv : v^k = 0 := by
    change ((AdjoinRoot.mk (X^k) X : V)^k)=0
    rw [←map_pow,AdjoinRoot.mk_self]
  let x : V := algebraMap K V t + algebraMap K V a * v
  let y : U := algebraMap K U a⁻¹ * (u - algebraMap K U t)
  have hx : aeval x ((X-C t)^k)=0 := by
    rw [map_pow,map_sub,aeval_X,aeval_C]
    dsimp [x]
    rw [add_sub_cancel_left,mul_pow,hv,mul_zero]
  have hy : aeval y (X^k : K[X])=0 := by
    rw [map_pow,aeval_X]
    dsimp [y]
    rw [mul_pow,hu,mul_zero]
  let f := AdjoinRoot.liftHom ((X-C t)^k) x hx
  let g := AdjoinRoot.liftHom (X^k : K[X]) y hy
  have hf : f u = x := AdjoinRoot.liftHom_root ..
  have hg : g v = y := AdjoinRoot.liftHom_root ..
  have fc (b : K) : f (algebraMap K U b) = algebraMap K V b := f.commutes b
  have gc (b : K) : g (algebraMap K V b) = algebraMap K U b := g.commutes b
  have hVa : algebraMap K V a⁻¹ * algebraMap K V a = 1 := by
    rw [←map_mul,inv_mul_cancel₀ ha,map_one]
  have hUa : algebraMap K U a * algebraMap K U a⁻¹ = 1 := by
    rw [←map_mul,mul_inv_cancel₀ ha,map_one]
  have h1 : f.comp g = AlgHom.id K V := by
    apply AdjoinRoot.algHom_ext
    change f (g v) = v
    rw [hg]
    change f (algebraMap K U a⁻¹ * (u - algebraMap K U t)) = v
    rw [map_mul,map_sub,hf,fc,fc]
    dsimp only [x]
    rw [add_sub_cancel_left,←mul_assoc,hVa,one_mul]
  have h2 : g.comp f = AlgHom.id K U := by
    apply AdjoinRoot.algHom_ext
    change g (f u) = u
    rw [hf]
    change g (algebraMap K V t + algebraMap K V a * v) = u
    rw [map_add,map_mul,hg,gc,gc]
    dsimp only [y]
    rw [←mul_assoc,hUa,one_mul,add_sub_cancel]
  let e := AlgEquiv.ofAlgHom f g h1 h2
  refine ⟨e,?_⟩
  have H : f.toRingHom.comp (AdjoinRoot.mk ((X-C t)^k)) =
      (AdjoinRoot.mk (X^k : K[X])).comp (affinePolynomial t a) := by
    apply Polynomial.ringHom_ext
    · intro b
      change f (AdjoinRoot.mk _ (C b)) = AdjoinRoot.mk (X^k) ((C b).comp (C t + C a * X))
      rw [Polynomial.C_comp]
      exact fc b
    · change f u = AdjoinRoot.mk (X^k) (X.comp (C t + C a * X))
      rw [hf,X_comp,map_add,map_mul]
      rfl
  exact fun p => RingHom.congr_fun H p

theorem local_coeff_rank_eq_field_jet {I : Type*} [Fintype I] [DecidableEq I]
    (B : Matrix I I K[X]) (t a : K) (ha : a≠0) (k : ℕ) :
    (localCoefficientMatrix B t a k).rank = RankBudget.jetLength B t k := by
  obtain ⟨e,he⟩ := affine_field_jet_equiv t a ha k
  let T := (LinearEquiv.piCongrRight fun _ : I => e.toLinearEquiv)
  let A := B.map (affinePolynomial t a)
  let Z : (I→PlainJet K k) →ₗ[K] (I→PlainJet K k) :=
    (A.map (AdjoinRoot.mk (X^k))).mulVecLin.restrictScalars K
  have h1 (v : I × Fin k→K) :
      (jetCoordinates k) ((localCoefficientMatrix B t a k).mulVecLin v)=Z (jetCoordinates k v) :=
    encodeJet_commutes A k v
  have h2 (v : I→RankBudget.Jet t k) :
      T (RankBudget.jetMul B t k v) = Z (T v) := by
    funext i
    change e.toRingHom ((B.map (AdjoinRoot.mk ((X-C t)^k)) *ᵥ v) i) =
      ((A.map (AdjoinRoot.mk (X^k))) *ᵥ (e.toRingHom ∘ v)) i
    rw [RingHom.map_mulVec e.toRingHom]
    congr 1
    ext j l
    exact he (B j l)
  exact (range_conjugate_equiv _ _ _ h1).finrank_eq.trans
    (range_conjugate_equiv _ _ _ h2).finrank_eq.symm

#print axioms affine_field_jet_equiv
#print axioms local_coeff_rank_eq_field_jet
end Paper5
