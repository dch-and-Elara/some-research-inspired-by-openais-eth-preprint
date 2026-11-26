import P5A11SharpCommonReduction

/-! Apply uniform reduction to the same ordinary integral image
lattice in its Smith basis. No reduction-basis receipt is supplied. -/
namespace Paper5.CommonJets
open scoped BigOperators Classical
open Module

variable {R : Type*} [CommRing R] {n r : ℕ}

theorem power_in_smith_coordinates (π : R) (P : ℕ)
    (N : Submodule R (Fin n→R)) (D : Basis.SmithNormalForm N (Fin n) r) (x : N) :
    (∃ y : Fin n→R, (x:Fin n→R)=π^P • y) ↔
      ∀ i : Fin r, π^P ∣ D.a i * D.bN.repr x i := by
  have hcoord (i : Fin r) : D.bM.repr (x:Fin n→R) (D.f i) =
      D.a i * D.bN.repr x i := by
    simpa only [map_smul,Finsupp.smul_apply,smul_eq_mul] using
      (D.repr_apply_embedding_eq_repr_smul x (i:=i))
  constructor
  · rintro ⟨y,hy⟩ i
    have h := congrArg (fun z=>D.bM.repr z (D.f i)) hy
    change D.bM.repr (x:Fin n→R) (D.f i)=D.bM.repr (π^P • y) (D.f i) at h
    rw [hcoord,map_smul,Finsupp.smul_apply,smul_eq_mul] at h
    exact ⟨_,h⟩
  · intro hx
    choose c hc using hx
    refine ⟨∑ i,c i • D.bM (D.f i),?_⟩
    calc
      (x:Fin n→R) = ∑ i,D.bN.repr x i • (D.bN i:Fin n→R) := by
        simpa only [Submodule.coe_sum,Submodule.coe_smul] using
          (congrArg Subtype.val (D.bN.sum_repr x)).symm
      _ = _ := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [D.snf,smul_smul,smul_smul,mul_comm (D.bN.repr x i),hc i]

variable [IsDomain R]

set_option maxHeartbeats 6000000 in
theorem smith_uniform_range (π : R) (hπ : π≠0) (P : ℕ)
    (N : Submodule R (Fin n→R)) (D : Basis.SmithNormalForm N (Fin n) r)
    (σ : Fin r→ℕ) (u : Fin r→Rˣ) (ha : ∀ i,D.a i=(u i:R)*π^(σ i)) :
    Nonempty (LinearMap.range ((uniformReduce π P n).comp N.subtype) ≃ₗ[R]
      CyclicGrid π (fun i=>P-σ i)) := by
  let F := (uniformReduce π P n).comp N.subtype
  let Q : N →ₗ[R] CyclicGrid π (fun i=>P-σ i) :=
    LinearMap.pi fun i =>
      ((Ideal.Quotient.mkₐ R (PowIdeal π (P-σ i))).toLinearMap).comp
        ((LinearMap.proj i).comp D.bN.equivFun.toLinearMap)
  have hQ (x : N) (i : Fin r) :
      Q x i = Ideal.Quotient.mk (PowIdeal π (P-σ i)) (D.bN.repr x i) := rfl
  have hzero (x : N) : Q x=0 ↔ ∀i,π^(P-σ i)∣D.bN.repr x i := by
    constructor
    · intro h i
      have he := congrFun h i
      rw [hQ,Pi.zero_apply,Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton] at he
      exact he
    · intro h
      funext i
      rw [hQ,Pi.zero_apply,Ideal.Quotient.eq_zero_iff_mem,Ideal.mem_span_singleton]
      exact h i
  have hk : LinearMap.ker F = LinearMap.ker Q := by
    ext x
    rw [LinearMap.mem_ker,LinearMap.mem_ker,hzero]
    change uniformReduce π P n (x:Fin n→R)=0 ↔ _
    rw [uniformReduce_zero_iff,power_in_smith_coordinates π P N D]
    apply forall_congr'
    intro i
    rw [ha,mul_assoc,(u i).isUnit.dvd_mul_left,pow_dvd_pow_mul_iff π hπ P (σ i)]
  have hsur : Function.Surjective Q := by
    intro y
    choose x hx using fun i=>
      (Ideal.Quotient.mk_surjective (I:=PowIdeal π (P-σ i))) (y i)
    refine ⟨D.bN.equivFun.symm x,?_⟩
    funext i
    rw [hQ,show D.bN.repr (D.bN.equivFun.symm x) i = x i from
      congrFun (D.bN.equivFun.apply_symm_apply x) i,hx]
  exact ⟨(LinearMap.quotKerEquivRange F).symm.trans
    ((Submodule.quotEquivOfEq (LinearMap.ker F) (LinearMap.ker Q) hk).trans
      (LinearMap.quotKerEquivOfSurjective Q hsur))⟩

#print axioms power_in_smith_coordinates
#print axioms smith_uniform_range
end Paper5.CommonJets
