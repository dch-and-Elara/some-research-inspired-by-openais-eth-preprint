import P5LiteralJets

/-! Ordinary coefficient coordinates for an actual truncated affine jet.
The argument works over every coefficient ring, including zero precision. -/
namespace Paper5
open scoped BigOperators Polynomial
open Polynomial Matrix

variable {S : Type*} [CommRing S]
variable {I : Type*} [Fintype I]

abbrev PlainJet (S : Type*) [CommRing S] (k : ℕ) := AdjoinRoot (X ^ k : S[X])

noncomputable def encodeJet (k : ℕ) : (I × Fin k→S) →ₗ[S] (I→PlainJet S k) :=
  LinearMap.pi fun i => (AdjoinRoot.mkₐ (X^k : S[X])).toLinearMap.comp (testVecLin k i)

omit [Fintype I] in
theorem encodeJet_injective (k : ℕ) : Function.Injective (encodeJet (S:=S) (I:=I) k) := by
  intro x y h
  funext j
  have he := congrFun h j.1
  change AdjoinRoot.mk (X^k) (testVec k x j.1) = AdjoinRoot.mk (X^k) (testVec k y j.1) at he
  have hz := (Polynomial.X_pow_dvd_iff.mp (AdjoinRoot.mk_eq_mk.mp he)) j.2.val j.2.isLt
  rw [coeff_sub,testVec_coeff,testVec_coeff] at hz
  exact sub_eq_zero.mp hz

omit [Fintype I] in
theorem encodeJet_surjective (k : ℕ) : Function.Surjective (encodeJet (S:=S) (I:=I) k) := by
  intro y
  choose p hp using fun i => AdjoinRoot.mk_surjective (y i)
  refine ⟨fun j => (p j.1).coeff j.2,?_⟩
  funext i
  change AdjoinRoot.mk (X^k) (testVec k (fun j : I × Fin k => (p j.1).coeff j.2) i) = y i
  rw [← hp i,AdjoinRoot.mk_eq_mk,Polynomial.X_pow_dvd_iff]
  intro d hd
  change (_ - p i).coeff (⟨d,hd⟩ : Fin k).val = 0
  rw [coeff_sub,testVec_coeff,sub_self]

noncomputable def jetCoordinates (k : ℕ) : (I × Fin k→S) ≃ₗ[S] (I→PlainJet S k) :=
  LinearEquiv.ofBijective (encodeJet k) ⟨encodeJet_injective k,encodeJet_surjective k⟩

theorem encodeJet_commutes (A : Matrix I I S[X]) (k : ℕ) (x : I × Fin k→S) :
    encodeJet k ((coefficientMatrix A k k) *ᵥ x) =
      A.map (AdjoinRoot.mk (X^k)) *ᵥ encodeJet k x := by
  funext i
  change AdjoinRoot.mk (X^k) (testVec k ((coefficientMatrix A k k) *ᵥ x) i) =
    (A.map (AdjoinRoot.mk (X^k)) *ᵥ (AdjoinRoot.mk (X^k) ∘ testVec k x)) i
  rw [← RingHom.map_mulVec,AdjoinRoot.mk_eq_mk,Polynomial.X_pow_dvd_iff]
  intro d hd
  change (_ - (A *ᵥ testVec k x) i).coeff (⟨d,hd⟩ : Fin k).val = 0
  rw [coeff_sub,testVec_coeff,coefficientMatrix_mulVec,sub_self]

noncomputable def affinePolynomial (t α : S) : S[X] →+* S[X] :=
  Polynomial.compRingHom (C t + C α * X)

theorem nativeObs_as_affine {R : Type*} [CommRing R] (π t α : R) (P k : ℕ) :
    (nativeObs π t α P k).toRingHom =
      (AdjoinRoot.mk (X^k : (Cyclic π P)[X])).comp
        ((Polynomial.mapRingHom (Ideal.Quotient.mk (PowIdeal π P))).comp (affinePolynomial t α)) := by
  apply Polynomial.ringHom_ext
  · intro a
    rw [show (nativeObs π t α P k).toRingHom (C a) = nativeObs π t α P k (C a) from rfl,nativeObs_coefficient]
    change _ = AdjoinRoot.mk (X^k) (((C a).comp (C t + C α * X)).map _)
    rw [Polynomial.C_comp,Polynomial.map_C]
    rfl
  · rw [show (nativeObs π t α P k).toRingHom X = nativeObs π t α P k X from rfl,nativeObs_X]
    change _ = AdjoinRoot.mk (X^k) ((X.comp (C t + C α * X)).map (Ideal.Quotient.mk (PowIdeal π P)))
    rw [X_comp,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_C,
      Polynomial.map_X,map_add,map_mul]
    rfl

#print axioms encodeJet_injective
#print axioms encodeJet_surjective
#print axioms jetCoordinates
#print axioms encodeJet_commutes
#print axioms nativeObs_as_affine
end Paper5
