import P5GenericReadoutUni
import P5A2SimulRank
import P5LiteralJets

/-! Canonical ordinary polynomial representatives in K[X][Y] for the
actual simultaneous quotient by X^k and Y^l. The coefficients are
lifted linearly, not as a multiplicative section. -/
namespace Paper5.GenericReadout
open Polynomial
open scoped BigOperators Polynomial Classical

variable {K : Type*} [Field K]

abbrev bivQuot (K : Type*) [Field K] (k l : ℕ) :
    K[X][X] →+* P5A2.Simultaneous K k l :=
  Ideal.Quotient.mk (P5A2.outerIdeal K l ⊔ P5A2.liftedIdeal K k)

noncomputable def outerRep (k l : ℕ) (u : P5A2.Simultaneous K k l) : (P5A2.Trunc K k)[X] :=
  AdjoinRoot.modByMonicHom (monic_X_pow l) (P5A2.twoAlg k l u)

noncomputable def bivRep (k l : ℕ) (u : P5A2.Simultaneous K k l) : K[X][X] :=
  testVec (I:=Unit) l (fun j=>uniRep k ((outerRep k l u).coeff j.2.val)) ()

theorem bivRep_coeff_inside (k l : ℕ) (u : P5A2.Simultaneous K k l) (j : Fin l) :
    (bivRep k l u).coeff j.val=uniRep k ((outerRep k l u).coeff j.val) :=
  testVec_coeff _ _ _ _

theorem bivRep_coeff_outside (k l : ℕ) (u : P5A2.Simultaneous K k l) (j : ℕ) (hj : l≤j) :
    (bivRep k l u).coeff j=0 :=
  testVec_other_coeff _ _ _ _ hj

theorem outerRep_coeff_outside {k l : ℕ} (hk : 0<k) (u : P5A2.Simultaneous K k l)
    (j : ℕ) (hj : l≤j) : (outerRep k l u).coeff j=0 := by
  letI : Nontrivial (P5A2.Trunc K k) := P5A2.trunc_nontrivial K k hk
  let z := P5A2.twoAlg k l u
  obtain ⟨q,hq⟩ := AdjoinRoot.mk_surjective z
  have h : outerRep k l u=q %ₘ (X:(P5A2.Trunc K k)[X])^l := by
    change AdjoinRoot.modByMonicHom (monic_X_pow l) z=_
    rw [←hq,AdjoinRoot.modByMonicHom_mk]
  rw [h]
  have hD := degree_modByMonic_lt q (monic_X_pow l)
  rw [degree_X_pow] at hD
  exact coeff_eq_zero_of_degree_lt (hD.trans_le (WithBot.coe_le_coe.mpr hj))

theorem bivRep_mk {k l : ℕ} (hk : 0<k) (u : P5A2.Simultaneous K k l) :
    bivQuot K k l (bivRep k l u)=u := by
  let Q := AdjoinRoot.mk ((X:K[X])^k)
  have h : (bivRep k l u).map Q=outerRep k l u := by
    apply Polynomial.ext
    intro j
    rw [Polynomial.coeff_map]
    by_cases hj : j<l
    · rw [bivRep_coeff_inside k l u ⟨j,hj⟩]
      exact uniRep_mk k _
    · have hge := Nat.le_of_not_gt hj
      rw [bivRep_coeff_outside k l u j hge,outerRep_coeff_outside hk u j hge,map_zero]
  apply (P5A2.twoAlg k l).injective
  change P5A2.twoEquiv k l (bivQuot K k l (bivRep k l u))=P5A2.twoAlg k l u
  rw [P5A2.twoEquiv_mk]
  change AdjoinRoot.mk ((X:(P5A2.Trunc K k)[X])^l) ((bivRep k l u).map Q)=_
  rw [h]
  exact AdjoinRoot.mk_leftInverse (monic_X_pow l) (P5A2.twoAlg k l u)

theorem bivRep_outer_degree (k l : ℕ) (u : P5A2.Simultaneous K k l) :
    (bivRep k l u).natDegree≤l-1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  exact bivRep_coeff_outside k l u j (by omega)

theorem bivRep_inner_degree (k l : ℕ) (u : P5A2.Simultaneous K k l) (j : ℕ) :
    ((bivRep k l u).coeff j).natDegree≤k-1 := by
  by_cases hj : j<l
  · rw [bivRep_coeff_inside k l u ⟨j,hj⟩]
    exact uniRep_degree k _
  · rw [bivRep_coeff_outside k l u j (Nat.le_of_not_gt hj),natDegree_zero]
    exact Nat.zero_le _

#print axioms bivRep_coeff_inside
#print axioms bivRep_coeff_outside
#print axioms outerRep_coeff_outside
#print axioms bivRep_mk
#print axioms bivRep_outer_degree
#print axioms bivRep_inner_degree
end Paper5.GenericReadout
