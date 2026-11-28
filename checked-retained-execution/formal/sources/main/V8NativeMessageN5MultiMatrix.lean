import V8NativeMessageN4Private
import P5HybridClosureAffine

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7600000
set_option maxRecDepth 4000

/-! N4 on one common matching with more than one native D coordinate.
The MAIN point factors split at the matching endpoints, not at a
hypothetical common MAIN group cut. The full D group product has
its own cut-specific rank deficit on the same matching. -/
namespace V8NativeMessage.N5
open scoped Classical BigOperators Polynomial
open Paper5.D1Literal GroupProducts SeparatedRank N4 V8NativeMessage.C3.NativeAssembly.MainScan
noncomputable section

section MatrixScale
variable {X Y R : Type*} [Fintype X] [Fintype Y] [Field R]

def scaleMatrix (B : Matrix X Y R) (row : X→R) (col : Y→R) : Matrix X Y R :=
  Matrix.of (fun x y=>row x*B x y*col y)

omit [Fintype X] [Fintype Y] in
theorem scaleMatrix_apply (B : Matrix X Y R) (row : X→R) (col : Y→R) (x : X) (y : Y) :
    scaleMatrix B row col x y=row x*B x y*col y := rfl

theorem scaleMatrix_rank (B : Matrix X Y R) (row : X→R) (col : Y→R) :
    (scaleMatrix B row col).rank≤B.rank := by
  have he : scaleMatrix B row col=(Matrix.diagonal row*B)*Matrix.diagonal col := by
    ext x y
    simp [scaleMatrix,Matrix.mul_diagonal,Matrix.diagonal_mul]
  rw [he]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
end MatrixScale

section Splice
variable {V I : Type*} {E : Finset (V×V)} (M : PinnedCNF.InducedMatching E I)

def rowCut (v : V) : Bool := decide (v∈Set.range (fun i=>M.endpoint (i,false)))

theorem matched_splice (x y : I→Bool) :
    N6.splice (rowCut M) (M.restrictSigns x (fun _=>true)) (M.restrictSigns (fun _=>true) y)=
      M.restrictSigns x y := by
  funext v
  by_cases hv : ∃ p,M.endpoint p=v
  · obtain ⟨⟨j,t⟩,rfl⟩ := hv
    cases t
    · have hh : M.endpoint (j,false)∈Set.range (fun i=>M.endpoint (i,false)) := ⟨j,rfl⟩
      simp [N6.splice,rowCut,hh]
    · have hh : M.endpoint (j,true)∉Set.range (fun i=>M.endpoint (i,false)) := by
        intro h
        obtain ⟨k,hk⟩ := h
        exact Bool.false_ne_true (congrArg Prod.snd (M.endpoint.injective hk))
      simp [N6.splice,rowCut,hh]
  · have hd : ¬∃ p,M.endpoint p=v := hv
    simp [N6.splice,M.restrict_outside x y hd,M.restrict_outside x (fun _=>true) hd,
      M.restrict_outside (fun _=>true) y hd]
end Splice

variable {V : Type} [Fintype V] [DecidableEq V] {F : Finset (V×V)}
  {reg : ∀ v,GraphCutMoments.degree F v=3} {f : ℤ[X]}
  {P : RootPacking F reg f} {i : rootKept F f}
  {I : Type*} [Fintype I] (M : PinnedCNF.InducedMatching F I)
  {K : Type*} [Field K] [Algebra ℚ K] (B : Block P i K)

def Dmatrix : Matrix (I→Bool) (I→Bool) K :=
  Matrix.of fun x y=>nativeD B.dFactors (M.restrictSigns x y)

def asGroupTerm : GroupTerm (rootLabels F reg f P) K where
  coordinate := i
  coeff := 1
  factor := B.dFactors

theorem Dmatrix_exact (symbols : rootKept F f→Finset (Fin 64)) :
    Dmatrix M B=(((asGroupTerm B).toVertexTerm symbols).onTransversal M.endpoint).matrix := by
  ext x y
  rw [VertexTerm.onTransversal_apply,GroupTerm.toVertexTerm_value]
  simp only [Dmatrix,Matrix.of_apply,GroupTerm.value,asGroupTerm,one_mul,nativeD]
  rfl

theorem Dmatrix_deficit (symbols : rootKept F f→Finset (Fin 64)) (d : ℕ)
    (hd : d≤endpointImbalance M.endpoint (EmpiricalCutMoments.labelCut
      (rootLabels F reg f P) id symbols i)) :
    (Dmatrix M B).rank≤2^(Fintype.card I-d) := by
  rw [Dmatrix_exact M B symbols]
  exact Paper5.HybridClosure.matching_group_term_rank (asGroupTerm B) symbols M.endpoint d hd

def mainMat : Matrix (I→Bool) (I→Bool) K :=
  Matrix.of fun x y=>sourceValue B (M.restrictSigns x y)

def rowPointProduct (q : Choices B) (x : I→Bool) : Jet B.kept :=
  shrink B.keep (∏ g,N6.leftPoint B.tuple reg B.accepted B.points g (q g)
    (rowCut M) (M.restrictSigns x (fun _=>true)))

def colPointProduct (q : Choices B) (y : I→Bool) : Jet B.kept :=
  shrink B.keep (∏ g,N6.rightPoint B.tuple reg B.accepted B.points g (q g)
    (rowCut M) (M.restrictSigns (fun _=>true) y))

omit [Fintype I] in
theorem one_choice_splices (q : Choices B) (x y : I→Bool) :
    shrink B.keep (∏ g,N6.entry B.tuple reg B.accepted B.points g (q g) (M.restrictSigns x y)) =
      rowPointProduct M B q x * colPointProduct M B q y := by
  rw [rowPointProduct,colPointProduct,←map_mul,←Finset.prod_mul_distrib]
  apply congrArg (shrink B.keep)
  apply Finset.prod_congr rfl
  intro g _
  rw [←N6.point_factors,matched_splice]

def rowCoefficient (q : Choices B) (j : Fin B.kept) (x : I→Bool) : K :=
  B.coefficient*algebraMap ℚ K ((V8NativeMessage.C3.jetBasis ℚ B.kept).repr
    (rowPointProduct M B q x) j)

def colCoefficient (q : Choices B) (j : Fin B.kept) (y : I→Bool) : K :=
  B.read (V8NativeMessage.C3.jetBasis ℚ B.kept j * colPointProduct M B q y)

omit [Fintype I] in
theorem sample_rank_expansion :
    mainMat M B=∑ q : Choices B,∑ j : Fin B.kept,
      scaleMatrix (Dmatrix M B) (rowCoefficient M B q j) (colCoefficient M B q j) := by
  ext x y
  simp only [mainMat,Matrix.of_apply,sourceValue,mainValue,Matrix.sum_apply,scaleMatrix_apply,Dmatrix]
  rw [completed_choices,map_sum,map_sum,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  rw [one_choice_splices M B q x y]
  let basis := V8NativeMessage.C3.jetBasis ℚ B.kept
  let u := rowPointProduct M B q x
  let v := colPointProduct M B q y
  have h : B.read (u*v)=∑ j,algebraMap ℚ K (basis.repr u j)*B.read (basis j*v) := by
    conv_lhs => rw [←basis.sum_repr u]
    rw [Finset.sum_mul,map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_mul_assoc,LinearMap.map_smul,Algebra.smul_def]
  change B.coefficient*B.read (u*v)*_ = _
  rw [h,Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  unfold rowCoefficient colCoefficient
  ring

theorem mixed_deficit_rank (symbols : rootKept F f→Finset (Fin 64)) (d : ℕ)
    (hGap : d≤endpointImbalance M.endpoint (EmpiricalCutMoments.labelCut
      (rootLabels F reg f P) id symbols i)) :
    (mainMat M B).rank≤privateCapacity B*2^(Fintype.card I-d) := by
  rw [sample_rank_expansion]
  apply (V8CapacityUnified.U7.rank_sum_le Finset.univ _).trans
  let s := 2^(Fintype.card I-d)
  calc
    _ ≤ ∑ _q : Choices B,B.kept*s := by
      apply Finset.sum_le_sum
      intro q _
      apply (V8CapacityUnified.U7.rank_sum_le Finset.univ _).trans
      calc
        _ ≤ ∑ _j : Fin B.kept,s := by
          apply Finset.sum_le_sum
          intro j _
          exact (scaleMatrix_rank _ _ _).trans (Dmatrix_deficit M B symbols d hGap)
        _ = _ := by simp
    _ = _ := by simp [privateCapacity,Choices,Fintype.card_pi,s,mul_left_comm,mul_assoc]

#print axioms scaleMatrix_rank
#print axioms matched_splice
#print axioms Dmatrix_exact
#print axioms Dmatrix_deficit
#print axioms one_choice_splices
#print axioms sample_rank_expansion
#print axioms mixed_deficit_rank
end
end V8NativeMessage.N5