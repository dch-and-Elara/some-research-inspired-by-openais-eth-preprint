import J6R22ActiveUnit
import J6R9RecursiveProbes

/-! Literal Lagrange basis with specified actual finite inverses.
This agrees with the printed unit-separated Vandermonde decoder,
also over rings with zero divisors. No inverse matrix is a runtime
primitive in the inverse/difference receipts below. -/
namespace J6R22Active
open scoped BigOperators Polynomial
open Polynomial A1R10 A1R11 A1R12 AOracleMachineTime AOracleCoordinates
open NativeProbeRing

section Algebra
variable {R : Type*} [CommRing R] {d : ℕ}

noncomputable def lagFactor (x w : R) : R[X] := C w*(X-C x)
noncomputable def lagBasis (x : Fin (d+1)→R) (inv : Fin (d+1)→Fin (d+1)→R)
    (i : Fin (d+1)) : R[X] :=
  ∏ j ∈ Finset.univ.erase i,lagFactor (x j) (inv i j)

noncomputable def lagDecode (x y : Fin (d+1)→R)
    (inv : Fin (d+1)→Fin (d+1)→R) : R[X] :=
  ∑ i, C (y i)*lagBasis x inv i

theorem lagBasis_eval (x : Fin (d+1)→R) (inv : Fin (d+1)→Fin (d+1)→R)
    (h : ∀ i j,i≠j→(x i-x j)*inv i j=1) (i j : Fin (d+1)) :
    (lagBasis x inv i).eval (x j)=if i=j then 1 else 0 := by
  classical
  rw [lagBasis,eval_prod]
  by_cases eq : i=j
  · subst j
    rw [if_pos rfl]
    apply Finset.prod_eq_one
    intro w hw
    have hw' : i≠w := Ne.symm (Finset.mem_erase.mp hw).1
    simp only [lagFactor,eval_mul,eval_C,eval_sub,eval_X]
    rw [mul_comm,h i w hw']
  · rw [if_neg eq]
    refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm eq,Finset.mem_univ _⟩) ?_
    simp [lagFactor]

theorem lagDecode_eval (x y : Fin (d+1)→R)
    (inv : Fin (d+1)→Fin (d+1)→R)
    (h : ∀ i j,i≠j→(x i-x j)*inv i j=1) (j : Fin (d+1)) :
    (lagDecode x y inv).eval (x j)=y j := by
  classical
  simp only [lagDecode,eval_finset_sum,eval_mul,eval_C,lagBasis_eval x inv h]
  simp [mul_ite]

theorem lagDecode_degree (x y : Fin (d+1)→R)
    (inv : Fin (d+1)→Fin (d+1)→R) :
    (lagDecode x y inv).natDegree≤d := by
  classical
  apply natDegree_sum_le_of_forall_le
  intro i _
  apply natDegree_mul_le.trans
  rw [natDegree_C,zero_add]
  have hg : (lagBasis x inv i).natDegree≤(Finset.univ.erase i).card := by
    unfold lagBasis
    apply (natDegree_prod_le _ _).trans
    calc
      _ ≤ ∑ _j ∈ Finset.univ.erase i, (1:ℕ) := by
        apply Finset.sum_le_sum
        intro j _
        apply natDegree_mul_le.trans
        rw [natDegree_C,zero_add]
        exact natDegree_X_sub_C_le _
      _ = _ := by simp
  rw [Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,Fintype.card_fin] at hg
  simpa using hg

theorem lagDecode_is_native (x y : Fin (d+1)→R)
    (inv : Fin (d+1)→Fin (d+1)→R)
    (h : ∀ i j,i≠j→(x i-x j)*inv i j=1) :
    lagDecode x y inv = J6ActiveInterpolation.decoded x y := by
  have hu (i j : Fin (d+1)) (ne : i≠j) : IsUnit (x j-x i) :=
    ⟨⟨_,inv j i,h j i ne.symm,by rw [mul_comm,h j i ne.symm]⟩,rfl⟩
  have hy : (fun j=>(lagDecode x y inv).eval (x j))=y :=
    funext (lagDecode_eval x y inv h)
  simpa only [hy] using
    (J6ActiveInterpolation.decoded_exact x _ (lagDecode_degree x y inv) hu).symm
end Algebra

theorem chosenNode_diff_residue {p : ℕ} (hp : 0<p) (f : ℤ[X]) (hf : f.Monic)
    (hD : 0<f.natDegree) {d : ℕ} (fit : d≤2^f.natDegree) (i j : Fin d) (ne : i≠j) :
    residueMap p hp f
      (probe p f (chosenRep f.natDegree d fit i)-probe p f (chosenRep f.natDegree d fit j))≠0 := by
  rw [map_sub,sub_ne_zero]
  exact fun eq=>ne (chosenRep_injective _ _ _
    (binary_residues_injective p hp f hf hD eq))

theorem actual_pair_inverse {p ell : ℕ} (hp : 0<p) {fw : List (Word p)}
    (he : 0<fw.length) (hv : 0<ell) {f : ℤ[X]} (hf : f.Monic) (hD : fw.length=f.natDegree)
    [Fact (Irreducible (residuePoly f))]
    (hF : Modulus p hp fw=liftPoly p f) {d : ℕ} (fit : d≤2^f.natDegree)
    (i j : Fin d) (ne : i≠j) (xi xj : Meter (UVBlock fw ell))
    (hi : boxTransport hF (uvRead hp fw ell xi.result)=J6ActiveInterpolation.node p f ell d fit i)
    (hj : boxTransport hF (uvRead hp fw ell xj.result)=J6ActiveInterpolation.node p f ell d fit j) :
    let inv := unitInverse hp he hv (subM hp he xi xj)
    (uvRead hp fw ell xi.result-uvRead hp fw ell xj.result)*uvRead hp fw ell inv.result=1 ∧
    inv.steps≤xi.steps+xj.steps+subCap fw.length ell p hp+2+inverseFee fw.length ell p hp := by
  let a := probe p f (chosenRep f.natDegree d fit i)-probe p f (chosenRep f.natDegree d fit j)
  have read : boxTransport hF (uvRead hp fw ell (subM hp he xi xj).result)=
      J6ActiveInterpolation.scalarIn p f ell a := by
    rw [subM_value,map_sub,hi,hj]
    exact (map_sub _ _ _).symm
  obtain ⟨hy,ht⟩ := inverse_actual_scalar hp he hv hf hF hD (subM hp he xi xj) a
    (chosenNode_diff_residue hp f hf (hD ▸ he) fit i j ne) read
  constructor
  · apply boxTransport_injective hF
    rw [map_mul,map_one,← subM_value hp he xi xj,read]
    exact hy
  · exact ht.trans (Nat.add_le_add_right (subM_steps hp he xi xj) _)

#print axioms lagBasis_eval
#print axioms lagDecode_eval
#print axioms lagDecode_degree
#print axioms lagDecode_is_native
#print axioms chosenNode_diff_residue
#print axioms actual_pair_inverse
end J6R22Active


