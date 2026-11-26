import HermiteJetTransport
import P5A11FieldTransport

/-! Coefficient-first nonuniform scaled Hermite CRT. The output of the
equivalence is exactly the Hasse data after real affine substitution. -/
namespace Paper5.HermiteGeneric
open Polynomial Matrix
open scoped BigOperators Polynomial Classical

variable {K T : Type*} [Field K]

@[simp] theorem affine_C (t a c : K) : affinePolynomial t a (C c)=C c := C_comp

@[simp] theorem affine_X (t a : K) : affinePolynomial t a X=C t+C a*X := X_comp

noncomputable def affineLinear (t a : K) : K[X]→ₗ[K] K[X] where
  toFun := affinePolynomial t a
  map_add' := map_add _
  map_smul' c p := by
    simp only [RingHom.id_apply,smul_eq_C_mul,map_mul,affine_C]

noncomputable def scalarObserve (t a : K) (k : ℕ) : K[X]→ₗ[K] (Fin k→K) :=
  LinearMap.pi fun i => (lcoeff K i.val).comp (affineLinear t a)

theorem scalarObserve_apply (t a : K) (k : ℕ) (p : K[X]) (i : Fin k) :
    scalarObserve t a k p i=(affinePolynomial t a p).coeff i.val := rfl

noncomputable def polyOfCoeffs (k : ℕ) : (Fin k→K) →ₗ[K] K[X] :=
  (testVecLin (I:=Unit) k ()).comp (LinearMap.pi fun j : Unit × Fin k=>LinearMap.proj j.2)

theorem polyOfCoeffs_coeff (k : ℕ) (x : Fin k→K) (j : Fin k) :
    (polyOfCoeffs k x).coeff j.val=x j :=
  testVec_coeff k (fun z : Unit × Fin k=>x z.2) () j

theorem polyOfCoeffs_sum (k : ℕ) (x : Fin k→K) :
    polyOfCoeffs k x=∑j : Fin k, C (x j)*X^j.val := by
  change testVec k (fun z : Unit × Fin k=>x z.2) ()=_
  simp only [testVec,C_mul_X_pow_eq_monomial]

noncomputable def scalarEncode (k : ℕ) : (Fin k→K)→ₗ[K] PlainJet K k :=
  (AdjoinRoot.mkₐ (X^k : K[X])).toLinearMap.comp (polyOfCoeffs k)

theorem scalarEncode_injective (k : ℕ) : Function.Injective (scalarEncode (K:=K) k) := by
  intro x y h
  change AdjoinRoot.mk (X^k) (polyOfCoeffs k x)=AdjoinRoot.mk (X^k) (polyOfCoeffs k y) at h
  have hz := Polynomial.X_pow_dvd_iff.mp (AdjoinRoot.mk_eq_mk.mp h)
  funext i
  have he := hz i.val i.isLt
  rw [coeff_sub,polyOfCoeffs_coeff,polyOfCoeffs_coeff,sub_eq_zero] at he
  exact he

theorem scalarEncode_observe (t a : K) (k : ℕ) (p : K[X]) :
    scalarEncode k (scalarObserve t a k p) = AdjoinRoot.mk (X^k) (affinePolynomial t a p) := by
  change AdjoinRoot.mk (X^k) (polyOfCoeffs k (scalarObserve t a k p))=_
  apply AdjoinRoot.mk_eq_mk.mpr
  apply Polynomial.X_pow_dvd_iff.mpr
  intro j hj
  let i : Fin k := ⟨j,hj⟩
  change (polyOfCoeffs k (scalarObserve t a k p)-affinePolynomial t a p).coeff i.val=0
  rw [coeff_sub,polyOfCoeffs_coeff,scalarObserve_apply,sub_self]

theorem scalarEncode_surjective (k : ℕ) : Function.Surjective (scalarEncode (K:=K) k) := by
  intro z
  obtain ⟨p,rfl⟩ := AdjoinRoot.mk_surjective z
  refine ⟨fun i=>p.coeff i.val,?_⟩
  change AdjoinRoot.mk (X^k) (polyOfCoeffs k (fun i=>p.coeff i.val))=_
  apply AdjoinRoot.mk_eq_mk.mpr
  apply Polynomial.X_pow_dvd_iff.mpr
  intro j hj
  let i : Fin k := ⟨j,hj⟩
  change (polyOfCoeffs k (fun i=>p.coeff i.val)-p).coeff i.val=0
  rw [coeff_sub,polyOfCoeffs_coeff,sub_self]

noncomputable def scalarJetEquiv (k : ℕ) : (Fin k→K)≃ₗ[K] PlainJet K k :=
  LinearEquiv.ofBijective (scalarEncode k) ⟨scalarEncode_injective k,scalarEncode_surjective k⟩

noncomputable def nodeAffine (t α : K) (hα : α≠0) (k : ℕ) :
    HermiteJetTransport.Jet t k ≃ₐ[K] PlainJet K k :=
  Classical.choose (affine_field_jet_equiv t α hα k)

theorem nodeAffine_apply (t α : K) (hα : α≠0) (k : ℕ) (p : K[X]) :
    nodeAffine t α hα k (HermiteJetTransport.jet t k p) =
      AdjoinRoot.mk (X^k) (affinePolynomial t α p) :=
  Classical.choose_spec (affine_field_jet_equiv t α hα k) p

variable [Fintype T]

noncomputable def scaledHermite (t : T→K) (ht : Function.Injective t)
    (k : T→ℕ) (α : T→K) (hα : ∀u,α u≠0) :
    degreeLT K (∑ u,k u) ≃ₗ[K] ((u : T)→Fin (k u)→K) :=
  (HermiteJetTransport.hermiteEquiv t ht k).trans
    (LinearEquiv.piCongrRight fun u=>(nodeAffine (t u) (α u) (hα u) (k u)).toLinearEquiv.trans
      (scalarJetEquiv (K:=K) (k u)).symm)

theorem scaledHermite_apply (t : T→K) (ht : Function.Injective t)
    (k : T→ℕ) (α : T→K) (hα : ∀u,α u≠0)
    (p : degreeLT K (∑u,k u)) (u : T) :
    scaledHermite t ht k α hα p u = scalarObserve (t u) (α u) (k u) p.val := by
  apply (scalarJetEquiv (K:=K) (k u)).injective
  change scalarJetEquiv (k u) ((scalarJetEquiv (k u)).symm
    (nodeAffine (t u) (α u) (hα u) (k u) (HermiteJetTransport.jet (t u) (k u) p.val))) =
      scalarEncode (k u) (scalarObserve (t u) (α u) (k u) p.val)
  rw [LinearEquiv.apply_symm_apply,nodeAffine_apply,scalarEncode_observe]

#print axioms affineLinear
#print axioms polyOfCoeffs_coeff
#print axioms scalarEncode_observe
#print axioms nodeAffine_apply
#print axioms scaledHermite_apply
end Paper5.HermiteGeneric
