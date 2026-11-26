import P5A2Simultaneous

/-! Paper 5's rank formula transferred to the simultaneous quotient
with its literal bivariate monomials, not just a dimension-isomorphic ring. -/
namespace P5A2
open Polynomial Ideal Matrix Module
open scoped Classical BigOperators

variable {K : Type*} [Field K]

theorem ideal_two_generators (k l : ℕ) :
    outerIdeal K l ⊔ liftedIdeal K k =
      Ideal.span {((X : K[X][X])^l), C ((X : K[X])^k)} := by
  unfold liftedIdeal innerIdeal
  rw [Ideal.map_span]
  simp only [Set.image_singleton]
  rw [Ideal.span_insert]

noncomputable def twoAlg (k l : ℕ) : Simultaneous K k l ≃ₐ[K] Double K k l where
  toRingEquiv := twoEquiv k l
  commutes' c := by
    change twoEquiv k l (Ideal.Quotient.mk (outerIdeal K l ⊔ liftedIdeal K k) (C (C c))) = _
    rw [twoEquiv_mk,Polynomial.map_C]
    rfl

theorem twoEquiv_monomial {k l : ℕ} (hk : 0<k) (i : Fin k) (j : Fin l) :
    twoEquiv k l (Ideal.Quotient.mk (outerIdeal K l ⊔ liftedIdeal K k)
      (C ((X : K[X])^i.val) * (X : K[X][X])^j.val)) =
      pairBasis (K:=K) k l hk (i,j) := by
  rw [twoEquiv_mk,pairBasis_apply,powers_apply]
  simp only [Polynomial.map_mul,Polynomial.map_C,Polynomial.map_pow,Polynomial.map_X,
    outerPowers,powers_apply,map_mul]
  rfl

noncomputable def simultaneousBasis (k l : ℕ) (hk : 0<k) :
    Basis (Fin k × Fin l) K (Simultaneous K k l) :=
  (pairBasis (K:=K) k l hk).map (twoAlg (K:=K) k l).symm.toLinearEquiv

theorem simultaneous_basis_is_monomial {k l : ℕ} (hk : 0<k) (i : Fin k) (j : Fin l) :
    simultaneousBasis (K:=K) k l hk (i,j) =
      Ideal.Quotient.mk (outerIdeal K l ⊔ liftedIdeal K k)
        (C ((X : K[X])^i.val) * (X : K[X][X])^j.val) := by
  apply (twoAlg (K:=K) k l).injective
  rw [simultaneousBasis,Basis.map_apply]
  change (twoAlg k l) ((twoAlg k l).symm (pairBasis k l hk (i,j))) = _
  rw [AlgEquiv.apply_symm_apply]
  exact (twoEquiv_monomial (K:=K) hk i j).symm

set_option maxRecDepth 2000 in
set_option maxHeartbeats 4200000 in
theorem simultaneous_coordinate_rank {k l : ℕ} (hk : 0<k) (a : Fin k × Fin l) :
    let b := simultaneousBasis (K:=K) k l hk
    (pairing b (b.coord a)).rank = (a.1.val+1)*(a.2.val+1) := by
  let b := pairBasis (K:=K) k l hk
  let e := twoAlg (K:=K) k l
  let B := simultaneousBasis (K:=K) k l hk
  have hem : pairing B (B.coord a) = pairing b (b.coord a) := by
    apply Matrix.ext
    intro u v
    change B.coord a (B u * B v) = b.coord a (b u * b v)
    change ((b.map e.symm.toLinearEquiv).repr
        ((b.map e.symm.toLinearEquiv) u * (b.map e.symm.toLinearEquiv) v)) a =
      b.repr (b u*b v) a
    rw [Basis.map_repr,Basis.map_apply,Basis.map_apply]
    change b.repr (e (e.symm (b u)*e.symm (b v))) a = _
    rw [map_mul,e.apply_symm_apply,e.apply_symm_apply]
  change (pairing B (B.coord a)).rank = _
  rw [hem]
  exact double_coordinate_rank (K:=K) hk a

#print axioms ideal_two_generators
#print axioms twoAlg
#print axioms simultaneous_basis_is_monomial
#print axioms simultaneous_coordinate_rank
end P5A2
