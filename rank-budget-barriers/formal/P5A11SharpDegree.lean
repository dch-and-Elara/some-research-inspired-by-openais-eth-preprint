import P5A11SharpNewton
import P5A11SharpLocal

/-! True monomials and actual determinant degree of the proposed sharp
matrix. Monicity ensures no cancellation upon residue reduction. -/
namespace Paper5
open Polynomial Matrix
open scoped BigOperators Polynomial Classical

variable {R T I : Type*} [CommRing R] [Nontrivial R] [Fintype T]

omit [Nontrivial R] in
theorem sharpScalar_monic (t : T→R) (l : T→ℕ) :
    (sharpScalar t l).Monic := by
  unfold sharpScalar
  exact monic_prod_of_monic _ _ (fun u _=>(monic_X_sub_C (t u)).pow (l u))

theorem sharpScalar_degree (t : T→R) (l : T→ℕ) :
    (sharpScalar t l).natDegree=∑ u,l u := by
  unfold sharpScalar
  rw [natDegree_prod_of_monic _ _ (fun u _=>(monic_X_sub_C (t u)).pow (l u))]
  exact Finset.sum_congr rfl (fun u _=>by rw [(monic_X_sub_C (t u)).natDegree_pow,natDegree_X_sub_C,mul_one])

variable [LinearOrder T]

omit [Nontrivial R] in
theorem newtonColumn_monic (t : T→R) (k : T→ℕ) (u : T) (j : ℕ) :
    (newtonColumn t k u j).Monic := by
  unfold newtonColumn
  exact (monic_prod_of_monic _ _ (fun s _=>(monic_X_sub_C (t s)).pow (k s))).mul
    ((monic_X_sub_C (t u)).pow j)

theorem newtonColumn_degree (t : T→R) (k : T→ℕ) (u : T) (j : ℕ) :
    (newtonColumn t k u j).natDegree=(∑ v∈earlierNodes u,k v)+j := by
  unfold newtonColumn
  have h : (∏ s∈earlierNodes u,(X-C (t s))^(k s)).Monic :=
    monic_prod_of_monic _ _ (fun s _=>(monic_X_sub_C (t s)).pow (k s))
  rw [h.natDegree_mul ((monic_X_sub_C (t u)).pow j)]
  congr 1
  · rw [natDegree_prod_of_monic _ _ (fun s _=>(monic_X_sub_C (t s)).pow (k s))]
    exact Finset.sum_congr rfl (fun s _=>by rw [(monic_X_sub_C (t s)).natDegree_pow,natDegree_X_sub_C,mul_one])
  · rw [(monic_X_sub_C (t u)).natDegree_pow,natDegree_X_sub_C,mul_one]

variable [IsLocalRing R] [Fintype I] [DecidableEq I]

omit [LinearOrder T] [Nontrivial R] in
theorem sharp_residue_det (t : T→R) (l : T→ℕ) :
    ((sharpMatrix (I:=I) t l).map (Polynomial.mapRingHom (IsLocalRing.residue R))).det =
      ((sharpScalar t l).map (IsLocalRing.residue R))^(Fintype.card I) := by
  let f := Polynomial.mapRingHom (IsLocalRing.residue R)
  have h : (sharpMatrix (I:=I) t l).map f =
      Matrix.diagonal (fun _ : I=>f (sharpScalar t l)) := by
    ext i j
    by_cases h : i=j
    · subst j; simp [sharpMatrix]
    · simp [sharpMatrix,h]
  rw [h,Matrix.det_diagonal,Finset.prod_const,Finset.card_univ]
  rfl

omit [LinearOrder T] [Nontrivial R] in
theorem sharp_residue_det_monic (t : T→R) (l : T→ℕ) :
    ((sharpMatrix (I:=I) t l).map (Polynomial.mapRingHom (IsLocalRing.residue R))).det.Monic := by
  rw [sharp_residue_det]
  exact ((sharpScalar_monic t l).map (IsLocalRing.residue R)).pow _

omit [LinearOrder T] in
theorem sharp_residue_det_degree (t : T→R) (l : T→ℕ) :
    ((sharpMatrix (I:=I) t l).map (Polynomial.mapRingHom (IsLocalRing.residue R))).det.natDegree =
      Fintype.card I*(∑u,l u) := by
  rw [sharp_residue_det,((sharpScalar_monic t l).map (IsLocalRing.residue R)).natDegree_pow,
    (sharpScalar_monic t l).natDegree_map,sharpScalar_degree]

#print axioms sharpScalar_monic
#print axioms sharpScalar_degree
#print axioms newtonColumn_monic
#print axioms newtonColumn_degree
#print axioms sharp_residue_det_monic
#print axioms sharp_residue_det_degree
end Paper5
