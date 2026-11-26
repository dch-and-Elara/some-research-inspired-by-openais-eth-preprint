import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Tactic

/-! Source matrix step of v7 (A.10): residue injectivity yields a unit
coordinate minor, and a concrete triangular isomorphism gives a free
complement of the correct dimension. This does not assume a complement
or a nonzero minor as hidden input. -/
namespace Paper5
open scoped BigOperators

variable {K I J : Type*} [Field K] [Fintype I] [Fintype J] [DecidableEq J]

theorem exists_field_full_minor (A : Matrix I J K)
    (hA : Function.Injective A.mulVecLin) :
    ∃ e : J ↪ I, (A.submatrix e id).det ≠ 0 := by
  classical
  have hh : Module.finrank K (Submodule.span K (Set.range A.row)) = Fintype.card J := by
    rw [← A.rank_eq_finrank_span_row,Matrix.rank,LinearMap.finrank_range_of_inj hA]
    simp
  obtain ⟨f,hf,_,hlin⟩ := Submodule.exists_fun_fin_finrank_span_eq K (Set.range A.row)
  let e : J ≃ Fin (Module.finrank K (Submodule.span K (Set.range A.row))) :=
    (Fintype.equivFin J).trans (finCongr hh.symm)
  choose ι hι using fun i : J => hf (e i)
  have hinj : Function.Injective ι := by
    intro i j h
    apply e.injective
    apply hlin.injective
    exact (hι i).symm.trans ((congrArg A.row h).trans (hι j))
  refine ⟨⟨ι,hinj⟩,?_⟩
  have hrow : (A.submatrix ι id).row = f ∘ e := by
    funext i
    exact hι i
  change (A.submatrix ι id).det ≠ 0
  have hn : LinearIndependent K (A.submatrix ι id).row := by
    rw [hrow]
    exact hlin.comp e e.injective
  have hunit : IsUnit (A.submatrix ι id) := Matrix.linearIndependent_rows_iff_isUnit.mp hn
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero

variable {R : Type*} [CommRing R]

theorem exists_residue_unit_minor [IsLocalRing R] (A : Matrix I J R)
    (hA : Function.Injective (A.map (IsLocalRing.residue R)).mulVecLin) :
    ∃ e : J ↪ I, IsUnit (A.submatrix e id).det := by
  obtain ⟨e,he⟩ := exists_field_full_minor (A.map (IsLocalRing.residue R)) hA
  refine ⟨e,(IsLocalRing.residue_ne_zero_iff_isUnit _).mp ?_⟩
  rw [RingHom.map_det]
  exact he

variable {A B : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]

def triangular (e : A ≃ₗ[R] A) (f : A →ₗ[R] B) : (A × B) ≃ₗ[R] (A × B) where
  toFun x := (e x.1,f x.1+x.2)
  invFun y := (e.symm y.1,y.2-f (e.symm y.1))
  left_inv x := by
    rcases x with ⟨a,b⟩
    simp [add_comm]
  right_inv x := by
    rcases x with ⟨a,b⟩
    simp [sub_eq_add_neg,add_left_comm]
  map_add' x y := by
    ext
    · simp
    · simp only [Prod.fst_add,Prod.snd_add,map_add]
      ac_rfl
  map_smul' a x := by
    ext <;> simp [smul_add]

def arrowReindex {C D : Type*} (e : C ≃ D) : (C→R) ≃ₗ[R] (D→R) where
  toFun x d := x (e.symm d)
  invFun y c := y (e c)
  left_inv x := by funext i; simp
  right_inv y := by funext i; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {C : Type*}

noncomputable def unitMinorSplit (M : Matrix (J ⊕ C) J R)
    (h : IsUnit (M.submatrix Sum.inl id).det) :
    ((J→R) × (C→R)) ≃ₗ[R] ((J⊕C)→R) :=
  (triangular ((M.submatrix Sum.inl id).toLinearEquiv (Pi.basisFun R J) h)
    (M.submatrix Sum.inr id).toLin').trans
      (LinearEquiv.sumArrowLequivProdArrow J C R R).symm

theorem unitMinorSplit_apply_left (M : Matrix (J ⊕ C) J R)
    (h : IsUnit (M.submatrix Sum.inl id).det) (v : J→R) :
    unitMinorSplit M h (v,0) = M.mulVecLin v := by
  funext i
  cases i with
  | inl j =>
    change (M.submatrix Sum.inl id).toLinearEquiv (Pi.basisFun R J) h v j = _
    rw [Matrix.toLinearEquiv_apply,Matrix.toLin_eq_toLin',Matrix.toLin'_apply]
    rfl
  | inr c =>
    change ((M.submatrix Sum.inr id).toLin' v + 0) c = _
    rw [add_zero,Matrix.toLin'_apply]
    rfl

noncomputable def complementPick (e : J ↪ I) : (J ⊕ {i : I // i ∉ Set.range e}) ≃ I := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective e e.injective) (Equiv.refl _)).trans
    (Equiv.Set.sumCompl (Set.range e))

omit [Fintype I] [DecidableEq J] in
@[simp] theorem complementPick_inl (e : J ↪ I) (j : J) :
    complementPick e (.inl j) = e j := rfl

/-- Injectivity modulo the maximal ideal yields an actual integral free
split with exactly |I|-|J| complement coordinates. -/
theorem exists_split_from_residue [IsLocalRing R] (M : Matrix I J R)
    (hM : Function.Injective (M.map (IsLocalRing.residue R)).mulVecLin) :
    ∃ e : ((J→R) × (Fin (Fintype.card I-Fintype.card J)→R)) ≃ₗ[R] (I→R),
      ∀ v, e (v,0) = M.mulVecLin v := by
  classical
  obtain ⟨pick,hpick⟩ := exists_residue_unit_minor M hM
  let Z := {i : I // i ∉ Set.range pick}
  let ρ : (J ⊕ Z) ≃ I := complementPick pick
  have hc : Fintype.card Z = Fintype.card I-Fintype.card J := by
    have h := Fintype.card_congr ρ
    rw [Fintype.card_sum] at h
    change Fintype.card J + Fintype.card Z = _ at h
    omega
  let sw : Fin (Fintype.card I-Fintype.card J) ≃ Z :=
    ((Fintype.equivFin Z).trans (finCongr hc)).symm
  let M' := M.submatrix ρ id
  have hm' : IsUnit (M'.submatrix Sum.inl id).det := by
    have hm : M'.submatrix Sum.inl id = M.submatrix pick id := by
      ext i j
      exact congrArg (fun u => M u j) (complementPick_inl pick i)
    rwa [hm]
  refine ⟨((LinearEquiv.refl R (J→R)).prodCongr (arrowReindex (R:=R) sw)).trans
    ((unitMinorSplit M' hm').trans (arrowReindex ρ)),?_⟩
  intro v
  change arrowReindex ρ (unitMinorSplit M' hm' (v,0)) = M.mulVecLin v
  rw [unitMinorSplit_apply_left]
  funext i
  change ∑ j, M (ρ (ρ.symm i)) j*v j = ∑ j, M i j*v j
  rw [Equiv.apply_symm_apply]

#print axioms exists_field_full_minor
#print axioms exists_residue_unit_minor
#print axioms triangular
#print axioms unitMinorSplit_apply_left
#print axioms exists_split_from_residue
end Paper5
