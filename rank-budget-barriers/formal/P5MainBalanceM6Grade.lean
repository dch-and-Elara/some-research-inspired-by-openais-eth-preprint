import P5MainBalanceM6Scores

/-! Weighted V-grade of the printed sparse lift. A V-level s may use
two more input powers per unit of s; after trimming arbitrary omitted
terms are not used in the deformation degree calculation. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator Polynomial
open scoped BigOperators Classical

def Bigrade (p : Bivariate) (base slope : ℕ) : Prop :=
  ∀ j s,base+slope*s<j → (p.coeff j).coeff s=0

theorem bigrade_one (c : ℕ) : Bigrade 1 0 c := by
  intro j s hj
  have h : j≠0 := by omega
  simp [coeff_one,h]

theorem bigrade_multiply (p q : Bivariate) (a b c : ℕ)
    (hp : Bigrade p a c) (hq : Bigrade q b c) :
    Bigrade (p*q) (a+b) c := by
  intro j s hj
  rw [coeff_mul,finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro u hu
  have hU := Finset.mem_antidiagonal.mp hu
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro v hv
  have hV := Finset.mem_antidiagonal.mp hv
  by_cases h : a+c*v.1<u.1
  · rw [hp _ _ h,zero_mul]
  · have hq' : b+c*v.2<u.2 := by
      have hLeft : u.1≤a+c*v.1 := by omega
      have hSplit : c*v.1+c*v.2=c*s := by rw [←Nat.mul_add,hV]
      omega
    rw [hq _ _ hq',mul_zero]

theorem bigrade_sum {T : Type*} (S : Finset T) (p : T→Bivariate)
    (base slope : ℕ) (h : ∀ t∈S,Bigrade (p t) base slope) :
    Bigrade (∑ t∈S,p t) base slope := by
  intro j s hj
  rw [finset_sum_coeff,finset_sum_coeff]
  exact Finset.sum_eq_zero (fun t ht=> h t ht _ _ hj)

theorem bigrade_prod {T : Type*} (S : Finset T) (p : T→Bivariate) (base : T→ℕ)
    (slope : ℕ) (h : ∀ t∈S,Bigrade (p t) (base t) slope) :
    Bigrade (∏ t∈S,p t) (∑ t∈S,base t) slope := by
  induction S using Finset.induction_on with
  | empty => simpa using bigrade_one slope
  | insert a S ha ih =>
    rw [Finset.prod_insert ha,Finset.sum_insert ha]
    exact bigrade_multiply _ _ _ _ _ (h a (Finset.mem_insert_self _ _))
      (ih fun t ht=>h t (Finset.mem_insert_of_mem ht))

variable {E F V : Type*} {fowner : E→F} {sowner : V→F} [Fintype F]

def Recipe.graded (P : Recipe fowner sowner ℚ[X]) (base : F→ℕ) (slope : ℕ) : Prop :=
  ∀ f k (σ : {v : V // sowner v=f}→Bool) s,
    (P.coeff f k σ).coeff s≠0 → P.degree f k ≤ base f + slope * s

set_option maxHeartbeats 9800000 in
omit [Fintype F] in
theorem Recipe.factor_bigrade (P : Recipe fowner sowner ℚ[X]) (base : F→ℕ) (slope R : ℕ)
    (hP : P.graded base slope) (p : E→ℚ[X]) (hp : ∀ e,(p e).natDegree≤R)
    (f : F) (σ : {v : V // sowner v=f}→Bool) :
    Bigrade (P.factorScore f σ (fun e=>liftRow (p e))) (base f*R) (slope*R) := by
  unfold Recipe.factorScore
  apply bigrade_sum
  intro k _
  intro j s hj
  rw [←map_prod liftRow,coeff_C_mul]
  change (P.coeff f k σ * (((∏ z : Fin (P.degree f k),p (P.read f k z).val).map (C : ℚ→+*ℚ[X])).coeff j)).coeff s = 0
  rw [coeff_map,coeff_mul_C]
  by_cases hz : (P.coeff f k σ).coeff s=0
  · rw [hz,zero_mul]
  · have hdegree : (∏ z : Fin (P.degree f k),p (P.read f k z).val).natDegree≤P.degree f k*R := by
      calc
        _ ≤ ∑ z : Fin (P.degree f k),(p (P.read f k z).val).natDegree := Polynomial.natDegree_prod_le _ _
        _ ≤ ∑ _z : Fin (P.degree f k),R := Finset.sum_le_sum (fun z _=>hp _)
        _ = _ := by simp
    have hTop := Nat.mul_le_mul_right R (hP f k σ s hz)
    have hBound : (base f+slope*s)*R<j := by
      rw [Nat.add_mul,show slope*s*R=slope*R*s by ring]
      exact hj
    rw [coeff_eq_zero_of_natDegree_lt (hdegree.trans_lt (hTop.trans_lt hBound)),mul_zero]

set_option maxHeartbeats 9800000 in
theorem Recipe.evaluate_bigrade (P : Recipe fowner sowner ℚ[X]) (base : F→ℕ) (slope R : ℕ)
    (hP : P.graded base slope) (p : E→ℚ[X]) (hp : ∀ e,(p e).natDegree≤R)
    (σ : V→Bool) :
    Bigrade (P.evaluate σ (fun e=>liftRow (p e))) ((∑ f,base f)*R) (slope*R) := by
  rw [Finset.sum_mul]
  exact bigrade_prod Finset.univ _ _ _ (fun f _=>P.factor_bigrade base slope R hP p hp f _)

section Native
variable {W Copy I B : Type*} [Fintype E] [Fintype W] [Fintype Copy] [Fintype I] [Fintype B] [LinearOrder B]

theorem actualH_bigrade (L : SourceLayout E W F Copy I B) (mark : V↪E) (t : I→ℚ)
    (M : Mix Copy I B) (R : ℕ) (hR : ∀ e : E,∀ x : W→Bool,
      (physicalRow L t M e (qbits x)).natDegree≤R)
    (P : SourceRecipe L mark) (base : F→ℕ) (slope : ℕ) (hP : P.graded base slope) (σ : V→Bool) :
    Bigrade (actualH L mark t M P σ) ((∑ f,base f)*R) (slope*R) := by
  unfold actualH
  apply bigrade_sum
  intro x _
  exact P.evaluate_bigrade base slope R hP _ (fun e=>hR e x) σ

theorem retained_bigrade_bound {ell D a c : ℕ} (p : Bivariate)
    (h : Bigrade p a c) (hbound : a+c*(ell-1)<D)
    (s : Fin ell) :
    (vSlice s.val p).degree<↑D := by
  rw [degree_lt_iff_coeff_zero]
  intro j hj
  rw [coeff_vSlice]
  have hS : s.val≤ell-1 := by have := s.isLt; omega
  exact h j s (lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_left c hS) a)
    (hbound.trans_le hj))

end Native

#print axioms bigrade_multiply
#print axioms bigrade_prod
#print axioms Recipe.factor_bigrade
#print axioms Recipe.evaluate_bigrade
#print axioms actualH_bigrade
#print axioms retained_bigrade_bound
end P5MainBalance.M6
