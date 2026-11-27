import P5H4Rectangular
import P5H4FractionRank
import Mathlib.LinearAlgebra.FreeModule.PID

/-! §2.3: the smallest outer width over a quotient of a PID is exactly
the minimum fraction-field rank of its integral lifts. We use an actual
integral Smith basis to factor each lift, not a guessed lifting rule. -/
namespace Paper5.QuotientLiftWidth
open Matrix Module
open scoped BigOperators Classical

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 10000000
set_option maxRecDepth 4000

noncomputable section
variable {R K m n : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] [Fintype m] [Fintype n]
local notation "φ" => (algebraMap R K)

private def pidRows {r : ℕ} (e : Fin r ↪ m) (a : Fin r→R) :
    Matrix m (Fin r) R :=
  Matrix.of fun i j=>if i=e j then a j else 0

private theorem integral_chart (A : Matrix m n R) :
    ∃ (r : ℕ) (e : Fin r ↪ m) (a : Fin r→R) (U : Matrix m m R)
      (Z : Matrix m (Fin r) R) (C : Matrix (Fin r) n R)
      (T : Matrix n (Fin r) R),
      (∀ i,a i≠0) ∧ IsUnit U ∧ U*Z=pidRows e a ∧ Z*C=A ∧ A*T=Z := by
  let b := Pi.basisFun R m
  let N := LinearMap.range A.mulVecLin
  obtain ⟨r,S⟩ := N.smithNormalForm b
  let V : Fin r→m→R := fun j=>(S.bN j).val
  let Z : Matrix m (Fin r) R := b.toMatrix V
  let U : Matrix m m R := S.bM.toMatrix b
  have hz (i : m) (j : Fin r) : Z i j=(S.bN j).val i := by
    simp only [Z,V,b,Module.Basis.toMatrix_apply,Pi.basisFun_repr]
  have hb (B₁ B₂ : Basis m R (m→R)) : B₁.toMatrix B₂*B₂.toMatrix B₁=1 := by
    rw [Basis.toMatrix_mul_toMatrix,Basis.toMatrix_self]
  have hu : IsUnit U := ⟨⟨U,b.toMatrix S.bM,hb _ _,hb _ _⟩,rfl⟩
  have ha (i : Fin r) : S.a i≠0 := by
    intro hi
    apply S.bN.ne_zero i
    apply Subtype.ext
    simpa [hi] using S.snf i
  have hU : U*Z=pidRows S.f S.a := by
    change (S.bM.toMatrix b)*(b.toMatrix V)=_
    rw [Basis.toMatrix_mul_toMatrix]
    apply Matrix.ext
    intro i j
    rw [Basis.toMatrix_apply]
    change S.bM.repr ((S.bN j).val) i=if i=S.f j then S.a j else 0
    rw [S.snf,LinearEquiv.map_smul,Finsupp.smul_apply,Basis.repr_self,Finsupp.single_apply]
    by_cases h : i=S.f j
    · subst i
      simp
    · simp [h,Ne.symm h]
  have he (j : n) : (fun i=>A i j)∈N := by
    refine ⟨Pi.single j 1,?_⟩
    change A *ᵥ Pi.single j 1=_
    funext i
    simp [Matrix.mulVec_single]
  let J (j : n) : N := ⟨fun i=>A i j,he j⟩
  let C : Matrix (Fin r) n R := Matrix.of fun i j=>S.bN.repr (J j) i
  have hC : Z*C=A := by
    apply Matrix.ext
    intro i j
    have h := congrArg (fun (v : N)=>v.val i) (S.bN.sum_repr (J j))
    change (∑ k,Z i k*S.bN.repr (J j) k)=A i j
    simpa only [hz,Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,Pi.smul_apply,
      smul_eq_mul,mul_comm] using h
  have hh (j : Fin r) : ∃ z : n→R,A *ᵥ z=(S.bN j).val := (S.bN j).property
  choose z hz' using hh
  let T : Matrix n (Fin r) R := Matrix.of fun i j=>z j i
  have hT : A*T=Z := by
    apply Matrix.ext
    intro i j
    rw [hz]
    exact congrFun (hz' j) i
  exact ⟨r,S.f,S.a,U,Z,C,T,ha,hu,hU,hC,hT⟩

theorem factor_integrally_at_fraction_field_rank (A : Matrix m n R) :
    ∃ Z : Matrix m (Fin (A.map φ).rank) R,
      ∃ C : Matrix (Fin (A.map φ).rank) n R, A=Z*C := by
  obtain ⟨r,e,a,U,Z,C,T,ha,hU,hu,hC,hT⟩ := integral_chart A
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  have hrZ : (A.map φ).rank=(Z.map φ).rank := by
    refine le_antisymm ?_ ?_
    · rw [←hC,Matrix.map_mul]
      exact Matrix.rank_mul_le_left _ _
    · rw [←hT,Matrix.map_mul]
      exact Matrix.rank_mul_le_left _ _
  have hUZ : ((pidRows e a).map φ).rank=(Z.map φ).rank := by
    obtain ⟨u,rfl⟩ := hU
    rw [←hu,Matrix.map_mul]
    have hi : u.inv.map φ*u.val.map φ=1 := by
      rw [←Matrix.map_mul,u.inv_val]
      simp
    refine le_antisymm (Matrix.rank_mul_le_right _ _) ?_
    have he : u.inv.map φ*(u.val.map φ*Z.map φ)=Z.map φ := by
      rw [←Matrix.mul_assoc,hi,Matrix.one_mul]
    calc
      (Z.map φ).rank = _ := congrArg Matrix.rank he.symm
      _ ≤ _ := Matrix.rank_mul_le_right _ _
  have hsub : (((pidRows e a).map φ).submatrix e id)=diagonal (fun i=>φ (a i)) := by
    apply Matrix.ext
    intro i j
    change φ (if e i=e j then a j else 0)=_
    by_cases h : i=j
    · subst j
      simp
    · simp [h,e.injective.ne h]
  have hdiag : (diagonal (fun i=>φ (a i))).rank=r := by
    have hn (i) : φ (a i)≠0 := by
      intro hz
      exact ha i (hφ (hz.trans (map_zero φ).symm))
    simp [Matrix.rank_diagonal,hn]
  have hD : ((pidRows e a).map φ).rank=r := by
    refine le_antisymm (by simpa using Matrix.rank_le_card_width ((pidRows e a).map φ)) ?_
    calc
      r = (diagonal (fun i=>φ (a i))).rank := hdiag.symm
      _ = (((pidRows e a).map φ).submatrix e id).rank := congrArg Matrix.rank hsub.symm
      _ ≤ _ := Matrix.rank_submatrix_le e (Equiv.refl _) _
  have hr : (A.map φ).rank=r := hrZ.trans (hUZ.symm.trans hD)
  rw [hr]
  exact ⟨Z,C,hC.symm⟩

omit [IsDomain R] [IsPrincipalIdealRing R] in
private theorem matrix_lift {i j : Type*} (I : Ideal R) (P : Matrix i j (R ⧸ I)) :
    ∃ A : Matrix i j R,A.map (Ideal.Quotient.mk I)=P := by
  choose a ha using fun (x : i) (y : j)=>Ideal.Quotient.mk_surjective (I:=I) (P x y)
  exact ⟨Matrix.of a,Matrix.ext fun x y=>ha x y⟩

def QuotientWidthAt (I : Ideal R) (P : Matrix m n (R ⧸ I)) (w : ℕ) : Prop :=
  ∃ r≤w,∃ U : Matrix m (Fin r) (R ⧸ I),∃ V : Matrix (Fin r) n (R ⧸ I),P=U*V

def LiftRankAt (K : Type*) [Field K] [Algebra R K]
    (I : Ideal R) (P : Matrix m n (R ⧸ I)) (w : ℕ) : Prop :=
  ∃ A : Matrix m n R,A.map (Ideal.Quotient.mk I)=P ∧ (A.map (algebraMap R K)).rank≤w

theorem quotient_width_iff_integral_lift_rank (I : Ideal R) (P : Matrix m n (R ⧸ I)) (w : ℕ) :
    QuotientWidthAt I P w ↔ LiftRankAt K I P w := by
  constructor
  · rintro ⟨r,hr,U,V,hP⟩
    obtain ⟨U₀,hU⟩ := matrix_lift I U
    obtain ⟨V₀,hV⟩ := matrix_lift I V
    refine ⟨U₀*V₀,by rw [Matrix.map_mul,hU,hV,←hP],?_⟩
    rw [Matrix.map_mul]
    have hw : (U₀.map φ).rank≤r := by simpa using rank_le_card_width (U₀.map φ)
    exact (rank_mul_le_left _ _).trans (hw.trans hr)
  · rintro ⟨A,hA,hr⟩
    obtain ⟨U,V,hF⟩ := factor_integrally_at_fraction_field_rank (K:=K) A
    exact ⟨(A.map φ).rank,hr,U.map (Ideal.Quotient.mk I),V.map (Ideal.Quotient.mk I),
      by rw [←Matrix.map_mul,←hF,hA]⟩

/-- The same width is attained in both models and minimizes both. -/
theorem quotient_minimum_width_is_minimum_lift_rank (I : Ideal R) (P : Matrix m n (R ⧸ I)) :
    ∃ w, (∃ U : Matrix m (Fin w) (R ⧸ I),∃ V : Matrix (Fin w) n (R ⧸ I),P=U*V) ∧
      (∃ A : Matrix m n R,A.map (Ideal.Quotient.mk I)=P ∧ (A.map φ).rank=w) ∧
      ∀ v, QuotientWidthAt I P v → w≤v := by
  have existsRank : ∃ w,LiftRankAt K I P w := by
    obtain ⟨A,hA⟩ := matrix_lift I P
    exact ⟨(A.map φ).rank,A,hA,le_rfl⟩
  let w := Nat.find existsRank
  obtain ⟨A,hA,hRank⟩ := Nat.find_spec existsRank
  have minRank : w≤(A.map φ).rank := Nat.find_min' existsRank ⟨A,hA,le_rfl⟩
  have same : (A.map φ).rank=w := le_antisymm hRank minRank
  obtain ⟨U,V,hF⟩ := factor_integrally_at_fraction_field_rank (K:=K) A
  have factors : QuotientWidthAt I P ((A.map φ).rank) := by
    refine ⟨_,le_rfl,U.map (Ideal.Quotient.mk I),V.map (Ideal.Quotient.mk I),?_⟩
    rw [←Matrix.map_mul,←hF,hA]
  rw [same] at factors
  obtain ⟨r,hr,U',V',hm⟩ := factors
  have wr : w≤r := Nat.find_min' existsRank
    ((quotient_width_iff_integral_lift_rank (K:=K) I P r).mp ⟨r,le_rfl,U',V',hm⟩)
  have eq : r=w := le_antisymm hr wr
  subst r
  exact ⟨w,⟨U',V',hm⟩,⟨A,hA,same⟩,fun v hv=>Nat.find_min' existsRank
    ((quotient_width_iff_integral_lift_rank (K:=K) I P v).mp hv)⟩

#print axioms factor_integrally_at_fraction_field_rank
#print axioms quotient_width_iff_integral_lift_rank
#print axioms quotient_minimum_width_is_minimum_lift_rank
end
end Paper5.QuotientLiftWidth
