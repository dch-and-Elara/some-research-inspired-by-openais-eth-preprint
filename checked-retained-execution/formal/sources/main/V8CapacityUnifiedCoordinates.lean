import V8CapacityUnifiedOrder

/-! U3 with actual quotient coordinates; U5 as an isomorphism onto
the actual ambient attainable image, rather than a coordinate proxy. -/
namespace V8CapacityUnified
open scoped Classical BigOperators
open V8CapacityCRTJet V8CapacityCyclic V8CapacitySmith Module

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {O X I : Type*} [CommRing O] [Fintype X] [Fintype I]
variable (π : O) (p : ℕ)

local notation "B" => BaseMod O π p

/-- Reduce a genuine finite integral matrix, not individual symbolic
coordinates without a chosen ambient change of basis. -/
def reduceLinear (A : (X → O) →ₗ[O] (I → O)) :
    (X → B) →ₗ[B] (I → B) :=
  ((LinearMap.toMatrix' A).map (coeffMod O π p)).mulVecLin

@[simp] theorem reduceLinear_receipt (A : (X → O) →ₗ[O] (I → O)) (x : X → O) :
    reduceLinear π p A (residueRows π p x)=residueRows π p (A x) := by
  funext i
  change ((LinearMap.toMatrix' A).map (coeffMod O π p)).mulVec ((coeffMod O π p) ∘ x) i = _
  rw [← RingHom.map_mulVec,LinearMap.toMatrix'_mulVec]
  rfl

def reduceEquiv (A : (X → O) ≃ₗ[O] (I → O)) : (X → B) ≃ₗ[B] (I → B) where
  toFun := reduceLinear π p A.toLinearMap
  invFun := reduceLinear π p A.symm.toLinearMap
  left_inv x := by
    obtain ⟨u,rfl⟩ := residueRows_surj π p x
    rw [reduceLinear_receipt,reduceLinear_receipt]
    simp
  right_inv x := by
    obtain ⟨u,rfl⟩ := residueRows_surj π p x
    rw [reduceLinear_receipt,reduceLinear_receipt]
    simp
  map_add' := map_add (reduceLinear π p A.toLinearMap)
  map_smul' := map_smul (reduceLinear π p A.toLinearMap)

theorem reduceEquiv_receipt (A : (X → O) ≃ₗ[O] (I → O)) (x : X → O) :
    reduceEquiv π p A (residueRows π p x)=residueRows π p (A x) :=
  reduceLinear_receipt π p A.toLinearMap x

variable [IsDomain O] {E : Submodule O (X → O)} {n : ℕ}
variable {π} (S : Powered π E I n)

/-- The actual Smith basis chart reduced on the original ambient row
space. It is an isomorphism even when E has deficient rank. -/
def smithResidue : (X → B) ≃ₗ[B] (I → B) :=
  reduceEquiv π p S.chart.bM.equivFun

@[simp] theorem smithResidue_receipt (x : X → O) (i : I) :
    smithResidue p S (residueRows π p x) i=coeffMod O π p (coord S x i) := by
  change reduceEquiv π p S.chart.bM.equivFun (residueRows π p x) i=_
  rw [reduceEquiv_receipt]
  simp only [residueRows_apply,Basis.equivFun_apply,coord]

theorem residue_zero_iff (x : O) : coeffMod O π p x=0 ↔ π^p∣x := by
  simpa only [map_zero,sub_zero] using residues_eq_iff π p x 0

/-- Theorem U, coordinate criterion U3 for actual elements of R_p^X. -/
theorem U3_membership (hπ : π≠0) (L : ℕ) (v : X → B) :
    v∈attainable π L p E ↔
      (∀ i : Fin n, min p (S.exponent i-L) ≤
        truncatedOrder π p (smithResidue p S v (S.chart.f i))) ∧
      (∀ j : I, j∉Set.range S.chart.f → smithResidue p S v j=0) := by
  obtain ⟨x,rfl⟩ := residueRows_surj π p v
  rw [U1_lift,exact_saturation S hπ]
  simp only [smithResidue_receipt,order_of_lift_iff π p _ (min_le_left p _),residue_zero_iff]

/-- Restricting the Smith chart to non-outside indices is a true
bijection on U1, not a coordinate-dependent loss of information. -/
def U1_to_observed (hπ : π≠0) (L : ℕ) : attainable π L p E →ₗ[O] observed S L p where
  toFun v := ⟨fun i => smithResidue p S v.val (S.chart.f i), by
    have h := ((U3_membership p S hπ L v.val).mp v.property).1
    refine Submodule.mem_pi.mpr (fun i _ => ?_)
    obtain ⟨a,ha⟩ := (order_ge_iff π p _ (min_le_left p (S.exponent i-L))).mp (h i)
    obtain ⟨b,rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨b,?_⟩
    change coeffMod O π p (π^(min p (S.exponent i-L))*b)=_
    rw [map_mul]
    exact ha.symm⟩
  map_add' u v := by
    ext i
    change smithResidue p S (u.val+v.val) (S.chart.f i)=_
    simp
  map_smul' a v := by
    ext i
    change smithResidue p S ((algebraMap O B a) • v.val) (S.chart.f i)=_
    simp only [map_smul,Pi.smul_apply]
    rfl

theorem U1_to_observed_bijective (hπ : π≠0) (L : ℕ) :
    Function.Bijective (U1_to_observed p S hπ L) := by
  constructor
  · intro u v h
    apply Subtype.ext
    apply (smithResidue p S).injective
    funext j
    by_cases hj : j∈Set.range S.chart.f
    · obtain ⟨i,rfl⟩ := hj
      exact congrFun (congrArg Subtype.val h) i
    · rw [((U3_membership p S hπ L u.val).mp u.property).2 j hj,
        ((U3_membership p S hπ L v.val).mp v.property).2 j hj]
  · intro w
    obtain ⟨x,hx,hEq⟩ := (readable_obs S L p hπ w.val).mp w.property
    refine ⟨⟨residueRows π p x,(U1_lift π L p E x).mpr hx⟩,?_⟩
    apply Subtype.ext
    funext i
    change smithResidue p S (residueRows π p x) (S.chart.f i)=w.val i
    rw [smithResidue_receipt]
    exact hEq i

/-- Finite products are the indexed finite direct sum in U5. Inactive
entries have exponent zero and hence the zero cyclic quotient. -/
def U5_module (hπ : π≠0) (L : ℕ) :
    ((i : Fin n) → BaseMod O π (p-(S.exponent i-L))) ≃ₗ[O] attainable π L p E := by
  have he (i : Fin n) : p-(S.exponent i-L)=p-clipped S L p i := by
    unfold clipped
    omega
  let f (i : Fin n) : BaseMod O π (p-(S.exponent i-L)) ≃ₗ[O]
      BaseMod O π (p-clipped S L p i) := by
    rw [he i]
  exact (LinearEquiv.piCongrRight f).trans ((A4_modules S L p hπ).trans
    (LinearEquiv.ofBijective (U1_to_observed p S hπ L) (U1_to_observed_bijective p S hπ L)).symm)

#print axioms reduceLinear_receipt
#print axioms smithResidue_receipt
#print axioms U3_membership
#print axioms U1_to_observed_bijective
#print axioms U5_module
end
end V8CapacityUnified
