import P5A11SharpCommonReduction
import P5A11SharpActualDet

/-! Equal-precision (A.10) uses the literal untruncated Hasse matrix of
the SAME centres, scales, and derivative orders. The finite observation
is precisely its uniform coefficient reduction, with true jet encoding. -/
namespace Paper5.CommonJets
open Polynomial Matrix
open scoped BigOperators Polynomial Classical

variable {R T : Type*} [CommRing R] [Fintype T] [LinearOrder T]

noncomputable def nativeEncode (π : R) (P : ℕ) (k : T→ℕ) :
    CyclicGrid π (fun _ : Fin (∑u,k u)=>P) →ₗ[R] (∀ u,LocalJet π P (k u)) :=
  LinearMap.pi fun u =>
    (LinearMap.proj ()).comp
      (((encodeJet (I:=Unit) (S:=Cyclic π P) (k u)).restrictScalars R).comp
        (LinearMap.pi fun j : Unit × Fin (k u)=>LinearMap.proj ((orderedNodeEquiv k).symm ⟨u,j.2⟩)))

theorem nativeEncode_injective (π : R) (P : ℕ) (k : T→ℕ) :
    Function.Injective (nativeEncode π P k) := by
  intro x y h
  have hi (u : T) : ∀ (j : Unit × Fin (k u)),
      x ((orderedNodeEquiv k).symm ⟨u,j.2⟩)=y ((orderedNodeEquiv k).symm ⟨u,j.2⟩) := by
    have he : encodeJet (I:=Unit) (S:=Cyclic π P) (k u)
        (fun j=>x ((orderedNodeEquiv k).symm ⟨u,j.2⟩)) =
      encodeJet (I:=Unit) (S:=Cyclic π P) (k u)
        (fun j=>y ((orderedNodeEquiv k).symm ⟨u,j.2⟩)) := by
      funext v
      cases v
      exact congrFun h u
    exact congrFun (encodeJet_injective (I:=Unit) (S:=Cyclic π P) (k u) he)
  funext u
  let e := orderedNodeEquiv k
  have ht := hi (e u).1 ((),(e u).2)
  change x (e.symm (e u))=y (e.symm (e u)) at ht
  rwa [e.symm_apply_apply] at ht

omit [Fintype T] [LinearOrder T] in
theorem affine_testVec_coeff {n : ℕ} (t a : R) (x : Fin n→R) (j : ℕ) :
    (affinePolynomial t a (testVec (I:=Unit) n (fun p=>x p.2) ())).coeff j =
      ∑ i : Fin n,(affinePolynomial t a (X^i.val)).coeff j*x i := by
  rw [testVec,map_sum,Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro i _
  rw [←Polynomial.C_mul_X_pow_eq_monomial,map_mul]
  have he : affinePolynomial t a (C (x i)) = C (x i) :=
    Polynomial.C_comp
  rw [he,Polynomial.coeff_C_mul,mul_comm]

set_option maxHeartbeats 12000000 in
theorem native_observation_is_reduced_hasse (π : R) (P : ℕ) (t a : T→R) (k : T→ℕ) :
    (nativeEncode π P k).comp ((uniformReduce π P (∑u,k u)).comp
      (confluentHasseMatrix t a k).mulVecLin) =
        scalarObserve π t a (fun _=>P) k (∑u,k u) := by
  apply LinearMap.ext
  intro x
  funext u
  let p : R[X] := testVec (I:=Unit) (∑u,k u) (fun j=>x j.2) ()
  let e := orderedNodeEquiv k
  let c : Unit × Fin (k u)→Cyclic π P := fun j=>
    Ideal.Quotient.mk (PowIdeal π P) (((confluentHasseMatrix t a k)*ᵥ x) (e.symm ⟨u,j.2⟩))
  change AdjoinRoot.mk (X^(k u) : (Cyclic π P)[X]) (testVec (k u) c ()) =
    (nativeObs π (t u) (a u) P (k u)).toRingHom p
  rw [nativeObs_as_affine]
  change _ = AdjoinRoot.mk _ ((affinePolynomial (t u) (a u) p).map (Ideal.Quotient.mk (PowIdeal π P)))
  apply AdjoinRoot.mk_eq_mk.mpr
  apply Polynomial.X_pow_dvd_iff.mpr
  intro d hd
  let j : Fin (k u) := ⟨d,hd⟩
  change ((testVec (k u) c () -
    (affinePolynomial (t u) (a u) p).map (Ideal.Quotient.mk (PowIdeal π P))).coeff j.val)=0
  rw [Polynomial.coeff_sub,testVec_coeff (k u) c () j,Polynomial.coeff_map,sub_eq_zero]
  change Ideal.Quotient.mk (PowIdeal π P) (((confluentHasseMatrix t a k)*ᵥ x) (e.symm ⟨u,j⟩)) = _
  congr 1
  have h1 : (e (e.symm ⟨u,j⟩)).1=u := congrArg Sigma.fst (e.apply_symm_apply ⟨u,j⟩)
  have h2 : (e (e.symm ⟨u,j⟩)).2.val=j.val :=
    congrArg (fun z : NodeOrder k=>z.2.val) (e.apply_symm_apply ⟨u,j⟩)
  change (∑ i : Fin (∑u,k u),(affinePolynomial (t (e (e.symm ⟨u,j⟩)).1)
    (a (e (e.symm ⟨u,j⟩)).1) (X^i.val)).coeff (e (e.symm ⟨u,j⟩)).2.val*x i) = _
  simp_rw [h1,h2]
  exact (affine_testVec_coeff (t u) (a u) x j.val).symm

noncomputable def sourceImageEquiv (π : R) (P : ℕ) (t a : T→R) (k : T→ℕ) :
    LinearMap.range ((uniformReduce π P (∑u,k u)).comp
      (confluentHasseMatrix t a k).mulVecLin) ≃ₗ[R]
      LinearMap.range (scalarObserve π t a (fun _=>P) k (∑u,k u)) := by
  let F := (uniformReduce π P (∑u,k u)).comp (confluentHasseMatrix t a k).mulVecLin
  let Q := scalarObserve π t a (fun _=>P) k (∑u,k u)
  let E := nativeEncode π P k
  have hEq : E.comp F=Q := native_observation_is_reduced_hasse π P t a k
  have h (x : Fin (∑u,k u)→R) : E (F x)=Q x :=
    congrArg (fun f : (Fin (∑u,k u)→R) →ₗ[R] (∀ u,LocalJet π P (k u))=>f x) hEq
  let G : LinearMap.range F →ₗ[R] LinearMap.range Q :=
    (E.comp (LinearMap.range F).subtype).codRestrict (LinearMap.range Q) fun x=>by
      obtain ⟨z,hz⟩ := x.property
      exact ⟨z,(h z).symm.trans (congrArg E hz)⟩
  apply LinearEquiv.ofBijective G
  constructor
  · intro x y hxy
    apply Subtype.ext
    exact nativeEncode_injective π P k (congrArg Subtype.val hxy)
  · intro y
    obtain ⟨z,hz⟩ := y.property
    refine ⟨⟨F z,⟨z,rfl⟩⟩,?_⟩
    apply Subtype.ext
    exact (h z).trans hz

#print axioms nativeEncode_injective
#print axioms affine_testVec_coeff
#print axioms native_observation_is_reduced_hasse
#print axioms sourceImageEquiv
end Paper5.CommonJets
