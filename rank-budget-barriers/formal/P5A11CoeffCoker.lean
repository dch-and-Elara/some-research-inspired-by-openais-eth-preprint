import P5ObservationLength
import P5PrimitiveMinor

/-! Residue-rank width bound for the cokernel of an honest integral
ordinary coefficient matrix, used in the finite precision refinement.
No Smith pencil over the bivariate truncation ring is assumed. -/
namespace Paper5
open Matrix
open scoped BigOperators

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]

omit [IsLocalRing R] in
theorem length_of_power_killed_generators {Q : Type*} [AddCommGroup Q] [Module R Q]
    (π : R) (hπ : π≠0) (hmax : (Ideal.span ({π}:Set R)).IsMaximal)
    (P j : ℕ) (f : (Fin j→R) →ₗ[R] Q) (hf : Function.Surjective f)
    (kill : ∀ y : Q, π^P • y = 0) : Module.length R Q ≤ (j*P:ℕ) := by
  let G := PowerImage π P (Fin j→R)
  let f' := G.liftQ f (by
    rintro x ⟨y,rfl⟩
    change f (π^P • y)=0
    rw [map_smul,kill])
  have hsur : Function.Surjective f' := by
    intro y
    obtain ⟨x,rfl⟩ := hf y
    exact ⟨G.mkQ x,rfl⟩
  have h := Module.length_le_of_surjective f' hsur
  change Module.length R Q ≤ Module.length R (PowerQuot π P (Fin j→R)) at h
  rw [powerQuotFree_length π hπ hmax P,Fintype.card_fin] at h
  exact h

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def residueCoeffMap (π : R) (P : ℕ) :
    (I→R) →ₗ[R] (I→Cyclic π P) :=
  LinearMap.pi fun i => ((Ideal.Quotient.mkₐ R (PowIdeal π P)).toLinearMap).comp (LinearMap.proj i)

noncomputable def finiteCoeffMatrix (π : R) (P : ℕ) (M : Matrix I I R) :
    (I→Cyclic π P) →ₗ[R] (I→Cyclic π P) :=
  (M.map (Ideal.Quotient.mk (PowIdeal π P))).mulVecLin.restrictScalars R

theorem coker_matrix_reduction_bound (π : R) (hπ : π≠0)
    (hmax : (Ideal.span ({π}:Set R)).IsMaximal) (P : ℕ) (M : Matrix I I R) :
    Module.length R ((I→Cyclic π P) ⧸ LinearMap.range (finiteCoeffMatrix π P M)) ≤
      ((Fintype.card I - (M.map (IsLocalRing.residue R)).rank)*P : ℕ) := by
  classical
  let K := IsLocalRing.ResidueField R
  let V := M.map (IsLocalRing.residue R)
  let n := Fintype.card I
  let r := V.rank
  have hr : Module.finrank K (Submodule.span K (Set.range V.col)) = r :=
    (Matrix.rank_eq_finrank_span_cols V).symm
  obtain ⟨e,he,_,hei⟩ := Submodule.exists_fun_fin_finrank_span_eq K (Set.range V.col)
  let ψ : Fin r ≃ Fin (Module.finrank K (Submodule.span K (Set.range V.col))) := finCongr hr.symm
  choose i hi using fun j : Fin r => he (ψ j)
  let B := M.submatrix id i
  have hcol : (B.map (IsLocalRing.residue R)).col = e ∘ ψ := by
    exact funext hi
  have hI : Function.Injective (B.map (IsLocalRing.residue R)).mulVecLin :=
    Matrix.mulVec_injective_iff.mpr (hcol ▸ hei.comp ψ ψ.injective)
  have hsplit := exists_split_from_residue B hI
  rw [Fintype.card_fin] at hsplit
  obtain ⟨E,hE⟩ := hsplit
  let F := finiteCoeffMatrix π P M
  let ρ := residueCoeffMap (I:=I) π P
  let Q := LinearMap.range F
  let p := Q.mkQ.comp ρ
  have p_surj : Function.Surjective p := by
    intro y
    obtain ⟨a,rfl⟩ := Submodule.mkQ_surjective Q y
    choose b hb using fun i => Ideal.Quotient.mk_surjective (I:=PowIdeal π P) (a i)
    exact ⟨b,congrArg Q.mkQ (funext hb)⟩
  have hρ (x : I→R) : ρ (M.mulVecLin x) = F (ρ x) := by
    funext j
    exact (Ideal.Quotient.mk (PowIdeal π P)).map_mulVec M x j
  have hB (v : Fin r→R) : p (B.mulVecLin v)=0 := by
    let v' : I→R := ∑ j : Fin r, Pi.single (i j) (v j)
    have hMv : M.mulVecLin v'=B.mulVecLin v := by
      funext u
      rw [show M.mulVecLin v' u = (M *ᵥ v') u from rfl]
      simp only [v',Matrix.mulVec_sum,Finset.sum_apply,Matrix.mulVec_single]
      change (∑ j : Fin r,M u (i j) * v j) = _
      rfl
    rw [←hMv]
    change Q.mkQ (ρ (M.mulVecLin v')) = 0
    rw [hρ]
    apply LinearMap.mem_ker.mp
    rw [Submodule.ker_mkQ]
    exact ⟨ρ v',rfl⟩
  let f := p.comp (E.toLinearMap.comp (LinearMap.inr R (Fin r→R) (Fin (n-r)→R)))
  have hsur : Function.Surjective f := by
    intro y
    obtain ⟨x,rfl⟩ := p_surj y
    obtain ⟨⟨a,b⟩,rfl⟩ := E.surjective x
    refine ⟨b,?_⟩
    change p (E (0,b)) = p (E (a,b))
    rw [show (a,b)=(a,0)+(0,b) by simp, map_add,map_add,hE,hB,zero_add]
  have hkill : ∀ y : (I→Cyclic π P) ⧸ Q, π^P • y = 0 := by
    intro y
    obtain ⟨a,rfl⟩ := Submodule.mkQ_surjective Q y
    rw [←map_smul]
    have h : π^P • a = 0 := by
      funext i
      change π^P • a i = 0
      rw [Algebra.smul_def]
      change Ideal.Quotient.mk (PowIdeal π P) (π^P) * a i = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp)),zero_mul]
    rw [h,map_zero]
  exact length_of_power_killed_generators π hπ hmax P _ f hsur hkill

#print axioms length_of_power_killed_generators
#print axioms coker_matrix_reduction_bound
end Paper5
