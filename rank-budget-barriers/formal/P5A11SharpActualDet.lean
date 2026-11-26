import P5A11SharpOrdinals
import P5A11SharpChange
import P5A11SharpDegree

/-! The original integral, untruncated-in-pi monomial Hasse
evaluation determinant. Both row blocks and Newton columns use the
same concrete ordinal representation. -/
namespace Paper5
open Polynomial Matrix
open scoped BigOperators Polynomial Classical
variable {R T : Type*} [CommRing R] [Nontrivial R] [Fintype T] [LinearOrder T]

noncomputable def confluentHasseMatrix (t a : T→R) (k : T→ℕ) :
    Matrix (Fin (∑ u,k u)) (Fin (∑ u,k u)) R :=
  monomialHasseMatrix (fun i=> t (orderedNodeEquiv k i).1)
    (fun i=> a (orderedNodeEquiv k i).1) (fun i=>(orderedNodeEquiv k i).2.val)

private theorem fin_sum_choose_two (n : ℕ) :
    (∑ i : Fin n, i.val)=n.choose 2 := by
  change (∑ i : Fin n,id i.val)=_
  rw [Fin.sum_univ_eq_sum_range id n]
  change (∑ i∈Finset.range n,i)=n.choose 2
  rw [Finset.sum_range_id,Nat.choose_two_right]

omit [Nontrivial R] in
theorem newton_determinant_group_products (t a : T→R) (k : T→ℕ) :
    (newtonEvaluation t a k).det =
      (∏ u,(a u)^((k u).choose 2))*
      (∏ u, ∏ s∈earlierNodes u,(t u-t s)^(k s*k u)) := by
  rw [det_newtonEvaluation,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro u _
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,fin_sum_choose_two,
    Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Finset.prod_pow]
  simp only [←pow_mul]

theorem actual_confluent_determinant (t a : T→R) (k : T→ℕ) :
    (confluentHasseMatrix t a k).det =
      (∏ u,(a u)^((k u).choose 2))*
      (∏ u, ∏ s∈earlierNodes u,(t u-t s)^(k s*k u)) := by
  let e := orderedNodeEquiv k
  let p : Fin (∑ u,k u)→R[X] := fun i=>newtonColumn t k (e i).1 (e i).2.val
  have hp (i : Fin (∑u,k u)) : (p i).natDegree=i.val := by
    unfold p
    rw [newtonColumn_degree]
    exact block_prefix_is_ordinal k i
  have hm (i : Fin (∑u,k u)) : (p i).Monic := newtonColumn_monic _ _ _ _
  have hb := basisHasse_det_monic (fun i=>t (e i).1) (fun i=>a (e i).1)
    (fun i=>(e i).2.val) p hp hm
  have hc : basisHasseMatrix (fun i=>t (e i).1) (fun i=>a (e i).1)
      (fun i=>(e i).2.val) p = (newtonEvaluation t a k).submatrix e e := rfl
  rw [hc,Matrix.det_submatrix_equiv_self e] at hb
  exact hb.symm.trans (newton_determinant_group_products t a k)

#print axioms newton_determinant_group_products
#print axioms actual_confluent_determinant
end Paper5
