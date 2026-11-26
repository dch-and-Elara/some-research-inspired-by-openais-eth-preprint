import P5A11JetCoordinate

/-! The literal confluent Newton columns with consecutive copies of
each node. Vanishing below the jet order and the exact diagonal hold
over any commutative coefficient ring, regardless of residue collisions. -/
namespace Paper5
open Polynomial Matrix
open scoped BigOperators Polynomial Classical

variable {R T : Type*} [CommRing R] [Fintype T] [LinearOrder T]

noncomputable def earlierNodes (u : T) : Finset T := Finset.univ.filter (· < u)

noncomputable def newtonColumn (t : T→R) (k : T→ℕ) (u : T) (j : ℕ) : R[X] :=
  (∏ s∈earlierNodes u,(X-C (t s))^(k s))*(X-C (t u))^j

theorem affine_linear_factor (t a b : R) :
    affinePolynomial t a (X-C b)=C (t-b)+C a*X := by
  change (X-C b).comp (C t+C a*X)=_
  rw [sub_comp,X_comp,C_comp,map_sub]
  ring

theorem affine_own_factor (t a : R) : affinePolynomial t a (X-C t)=C a*X := by
  rw [affine_linear_factor,sub_self,map_zero,zero_add]

noncomputable def newtonPrefix (t a : T→R) (k : T→ℕ) (u : T) : R[X] :=
  ∏ s∈earlierNodes u,(C (t u-t s)+C (a u)*X)^(k s)

theorem newton_self_expansion (t a : T→R) (k : T→ℕ) (u : T) (j : ℕ) :
    affinePolynomial (t u) (a u) (newtonColumn t k u j) =
      (newtonPrefix t a k u*C ((a u)^j))*X^j := by
  unfold newtonColumn newtonPrefix
  simp only [map_mul,map_prod,map_pow,affine_own_factor,affine_linear_factor,mul_pow]
  ring

theorem newton_prefix_coeff_zero (t a : T→R) (k : T→ℕ) (u : T) :
    (newtonPrefix t a k u).coeff 0=∏ s∈earlierNodes u,(t u-t s)^(k s) := by
  unfold newtonPrefix
  rw [coeff_zero_eq_eval_zero,eval_prod]
  simp only [eval_pow,eval_add,eval_mul,eval_C,eval_X,mul_zero,add_zero]

theorem newton_diagonal_entry (t a : T→R) (k : T→ℕ) (u : T) (j : ℕ) :
    (affinePolynomial (t u) (a u) (newtonColumn t k u j)).coeff j =
      (a u)^j*∏ s∈earlierNodes u,(t u-t s)^(k s) := by
  rw [newton_self_expansion,coeff_mul_X_pow',if_pos le_rfl,Nat.sub_self,
    coeff_mul_C,newton_prefix_coeff_zero]
  exact mul_comm _ _

theorem newton_smaller_order_zero (t a : T→R) (k : T→ℕ) (u : T) (i j : ℕ)
    (h : i<j) :
    (affinePolynomial (t u) (a u) (newtonColumn t k u j)).coeff i=0 := by
  rw [newton_self_expansion,coeff_mul_X_pow',if_neg (not_le_of_gt h)]

theorem newton_earlier_node_zero (t a : T→R) (k : T→ℕ) (u v : T) (i j : ℕ)
    (huv : u<v) (hi : i<k u) :
    (affinePolynomial (t u) (a u) (newtonColumn t k v j)).coeff i=0 := by
  let U := earlierNodes v
  let f (s : T) := (affinePolynomial (t u) (a u) (X-C (t s)))^(k s)
  have hU : u∈U := Finset.mem_filter.mpr ⟨Finset.mem_univ _,huv⟩
  have hsplit : (∏ s∈U,f s)=f u*(∏ s∈U.erase u,f s) := by
    exact (Finset.mul_prod_erase _ _ hU).symm
  have hd : X^(k u) ∣ affinePolynomial (t u) (a u) (newtonColumn t k v j) := by
    unfold newtonColumn
    rw [map_mul,map_prod]
    simp only [map_pow]
    change X^k u ∣ (∏ s∈U,f s)*_
    rw [hsplit]
    unfold f
    rw [affine_own_factor,mul_pow]
    exact ⟨(C (a u))^(k u)*(∏ s∈U.erase u, f s)*
          (affinePolynomial (t u) (a u) (X-C (t v)))^j,by ring⟩
  exact (X_pow_dvd_iff.mp hd) i hi

#print axioms affine_linear_factor
#print axioms newton_self_expansion
#print axioms newton_diagonal_entry
#print axioms newton_smaller_order_zero
#print axioms newton_earlier_node_zero
end Paper5
