import P5OverlayScalarSubstitution

/-! The stated min(P,k) length for the actual observation of π+T at
the stated center and scale, not an abstract one-generator bound. -/
namespace Paper5.ObservationExamples
open Polynomial
open scoped Polynomial

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 4300

noncomputable section
variable {R : Type*} [CommRing R]

private theorem powerIdeal_antitone (π : R) {i j : ℕ} (h : i≤j) :
    PowIdeal π j≤PowIdeal π i := by
  apply Ideal.span_le.mpr
  intro x hx
  have he : x=π^j := by simpa only [Set.mem_singleton_iff] using hx
  rw [he]
  apply Ideal.mem_span_singleton.mpr
  exact ⟨π^(j-i),by rw [←pow_add,Nat.add_sub_of_le h]⟩

theorem powerIdeal_sup_is_minimum (π : R) (P k : ℕ) :
    PowIdeal π P ⊔ PowIdeal π k=PowIdeal π (min P k) := by
  rcases le_total P k with h|h
  · rw [min_eq_left h,sup_eq_left.mpr (powerIdeal_antitone π h)]
  · rw [min_eq_right h,sup_eq_right.mpr (powerIdeal_antitone π h)]

abbrev observedPiPlusT (π : R) (P k : ℕ) : LocalJet π P k :=
  nativeObs π 0 1 P k (Polynomial.C π+X)

abbrev NativeScalarCoker (π : R) (P k : ℕ) :=
  LocalJet π P k ⧸ Ideal.span ({observedPiPlusT π P k}:Set (LocalJet π P k))

theorem native_observes_pi_plus_T (π : R) (P k : ℕ) :
    observedPiPlusT π P k =
      jvar (Cyclic π P) k +
        algebraMap (Cyclic π P) (LocalJet π P k) (algebraMap R (Cyclic π P) π) := by
  simp [observedPiPlusT,nativeObs,add_comm,
    IsScalarTower.algebraMap_apply R (Cyclic π P) (LocalJet π P k)]

theorem scalar_ideal_is_actual_multiplication_image (π : R) (P k : ℕ)
    (x : LocalJet π P k) :
    x∈Ideal.span ({observedPiPlusT π P k}:Set (LocalJet π P k)) ↔
      ∃ y : LocalJet π P k,observedPiPlusT π P k*y=x := by
  rw [Ideal.mem_span_singleton]
  exact ⟨fun ⟨y,hy⟩=>⟨y,hy.symm⟩,fun ⟨y,hy⟩=>⟨y,hy.symm⟩⟩

def native_scalar_coker_to_cyclic (π : R) (P k : ℕ) :
    NativeScalarCoker π P k ≃ₐ[R] Cyclic π (min P k) := by
  let a : Cyclic π P := algebraMap R (Cyclic π P) π
  have hm : (PowIdeal π k).map (Ideal.Quotient.mkₐ R (PowIdeal π P)) =
      Ideal.span ({a^k}:Set (Cyclic π P)) := by
    rw [Ideal.map_span,Set.image_singleton,map_pow]
    rfl
  have he : CoeffQuot a k ≃ₐ[R] R ⧸ (PowIdeal π P ⊔ PowIdeal π k) := by
    have E := DoubleQuot.quotQuotEquivQuotSupₐ R (PowIdeal π P) (PowIdeal π k)
    rw [hm] at E
    exact E
  have f : SubstitutedJet a k ≃ₐ[R] CoeffQuot a k :=
    (scalar_substitution a k).restrictScalars R
  have hjet : NativeScalarCoker π P k ≃ₐ[R] SubstitutedJet a k := by
    unfold NativeScalarCoker relation
    rw [native_observes_pi_plus_T]
    rfl
  let out := (hjet.trans f).trans he
  change NativeScalarCoker π P k ≃ₐ[R] R ⧸ PowIdeal π (min P k)
  rw [←powerIdeal_sup_is_minimum]
  exact out

theorem native_scalar_coker_length (π : R) [IsDomain R] (hπ : π≠0)
    (hmax : (Ideal.span ({π}:Set R)).IsMaximal) (P k : ℕ) :
    Module.length R (NativeScalarCoker π P k) = (min P k:ℕ) :=
  (native_scalar_coker_to_cyclic π P k).toLinearEquiv.length_eq.trans
    (cyclic_length π hπ hmax (min P k))

#print axioms powerIdeal_sup_is_minimum
#print axioms native_observes_pi_plus_T
#print axioms scalar_ideal_is_actual_multiplication_image
#print axioms native_scalar_coker_length
end
end Paper5.ObservationExamples
