import P5A11SharpActualDet

/-! The printed numerical determinant-valuation formula. The additive
valuation is allowed to take infinity, as it does at a zero determinant.
No distinct-residue or unit-scale premise is needed for this identity. -/
namespace Paper5
open Polynomial Matrix
open scoped BigOperators Polynomial Classical

section Arithmetic
variable {R : Type*} [CommMonoid R]

theorem additive_value_product {I : Type*} (v : R→*Multiplicative ENat)
    (s : Finset I) (f : I→R) :
    Multiplicative.toAdd (v (∏ i∈s,f i))=∑ i∈s,Multiplicative.toAdd (v (f i)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.sum_insert hi,map_mul]
    change Multiplicative.toAdd (v (f i))+Multiplicative.toAdd (v (∏ j∈s,f j))=_
    rw [ih]

theorem additive_value_power (v : R→*Multiplicative ENat) (x : R) (a : ℕ) :
    Multiplicative.toAdd (v (x^a))=a • Multiplicative.toAdd (v x) := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ,map_mul]
    change Multiplicative.toAdd (v (x^a))+Multiplicative.toAdd (v x)=_
    rw [ih,succ_nsmul,add_comm]

end Arithmetic

variable {R T : Type*} [CommRing R] [Nontrivial R] [Fintype T] [LinearOrder T]

theorem actual_confluent_determinant_valuation (val : R→*Multiplicative ENat)
    (t a : T→R) (k : T→ℕ) :
    Multiplicative.toAdd (val (confluentHasseMatrix t a k).det) =
      (∑ u,((k u).choose 2:ENat)*Multiplicative.toAdd (val (a u)))+
      (∑ u,∑ s∈earlierNodes u,(k s*k u:ℕ) • Multiplicative.toAdd (val (t u-t s))) := by
  rw [actual_confluent_determinant,map_mul]
  change Multiplicative.toAdd (val (∏ u,(a u)^((k u).choose 2)))+
    Multiplicative.toAdd (val (∏ u, ∏ s∈earlierNodes u,(t u-t s)^(k s*k u)))=_
  simp_rw [additive_value_product,additive_value_power,nsmul_eq_mul]

#print axioms actual_confluent_determinant_valuation
end Paper5
