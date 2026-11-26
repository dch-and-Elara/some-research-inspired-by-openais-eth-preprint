import P5SmithExtraction

/-! Actual uniform coefficient reduction on the untruncated integral
receiving vector. Its kernel is the same power lattice in every basis. -/
namespace Paper5.CommonJets
open scoped BigOperators Classical
open Module

variable {R : Type*} [CommRing R]

noncomputable def uniformReduce (π : R) (P n : ℕ) :
    (Fin n→R) →ₗ[R] CyclicGrid π (fun _ : Fin n=>P) :=
  LinearMap.pi fun i => ((PowIdeal π P : Submodule R R).mkQ).comp (LinearMap.proj i)

theorem uniformReduce_zero_iff (π : R) (P n : ℕ) (x : Fin n→R) :
    uniformReduce π P n x=0 ↔ ∃ y : Fin n→R, x=(π^P) • y := by
  constructor
  · intro hx
    have hd (i : Fin n) : π^P ∣ x i := by
      have he : Ideal.Quotient.mk (PowIdeal π P) (x i)=0 := congrFun hx i
      exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp he)
    choose y hy using hd
    exact ⟨y,funext hy⟩
  · rintro ⟨y,rfl⟩
    funext i
    change Ideal.Quotient.mk (PowIdeal π P) (π^P*y i)=0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨y i,rfl⟩)

theorem reduced_image_from_range {n : ℕ} (π : R) (P : ℕ)
    (f : (Fin n→R) →ₗ[R] (Fin n→R)) :
    LinearMap.range ((uniformReduce π P n).comp (LinearMap.range f).subtype) =
      LinearMap.range ((uniformReduce π P n).comp f) := by
  ext z
  constructor
  · rintro ⟨⟨x,⟨w,rfl⟩⟩,hx⟩
    exact ⟨w,hx⟩
  · rintro ⟨w,hw⟩
    exact ⟨⟨f w,⟨w,rfl⟩⟩,hw⟩

theorem zero_of_cyclic_zero (π : R) (x : Cyclic π 0) : x=0 := by
  haveI : Subsingleton (Cyclic π 0) := by
    change Subsingleton (R ⧸ (Ideal.span ({π^0}:Set R)))
    rw [pow_zero,Ideal.span_singleton_one]
    infer_instance
  exact Subsingleton.elim _ _

#print axioms uniformReduce_zero_iff
#print axioms reduced_image_from_range
#print axioms zero_of_cyclic_zero
end Paper5.CommonJets
