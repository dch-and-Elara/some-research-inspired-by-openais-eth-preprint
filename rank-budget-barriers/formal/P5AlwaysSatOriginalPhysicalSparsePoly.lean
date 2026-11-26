import P5AlwaysSatOriginalPhysicalFibre
import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.Algebra.Field.ZMod

/-! The actual MAIN sparse branch uses the violation *polynomial* of
each cloned clause. The all-literal monomial has coefficient a unit
for either sign of a pin, so no literal disappears from the scope. -/
namespace Paper5.AlwaysSatOriginal.Physical
open scoped BigOperators Classical

section Polynomial
open MvPolynomial
variable {W K : Type*}

noncomputable def falseLiteral [CommRing K] (p : W×Bool) : MvPolynomial W K :=
  if p.2 then 1-X p.1 else X p.1

noncomputable def violation [CommRing K] (l : List (W×Bool)) : MvPolynomial W K :=
  (l.map falseLiteral).prod

noncomputable def topExponent (l : List (W×Bool)) : W→₀ℕ :=
  (l.map (fun p=>Finsupp.single p.1 1)).sum

def topSign [CommRing K] (l : List (W×Bool)) : K :=
  (l.map (fun p=>if p.2 then -1 else 1)).prod

theorem violation_degree_le [CommRing K] [Nontrivial K] (l : List (W×Bool)) : (violation (K:=K) l).totalDegree≤l.length := by
  induction l with
  | nil => simp [violation]
  | cons p l ih =>
    have d : (falseLiteral (K:=K) p).totalDegree≤1 := by
      cases h : p.2
      · simp [falseLiteral,h,MvPolynomial.totalDegree_X]
      · simpa [falseLiteral,h,MvPolynomial.totalDegree_X] using
          (MvPolynomial.totalDegree_sub (1 : MvPolynomial W K) (X p.1))
    change (falseLiteral (K:=K) p * violation (K:=K) l).totalDegree≤l.length+1
    exact (MvPolynomial.totalDegree_mul _ _).trans ((Nat.add_le_add d ih).trans (by omega))

theorem exponent_weight (l : List (W×Bool)) :
    (topExponent l).sum (fun _ n=>n)=l.length := by
  induction l with
  | nil => simp [topExponent]
  | cons p l ih =>
    change (Finsupp.single p.1 1+topExponent l).sum (fun _ n=>n)=l.length+1
    rw [Finsupp.sum_add_index']
    · rw [Finsupp.sum_single_index (by rfl),ih,Nat.add_comm]
    · intro i; rfl
    · intro i a b; rfl

theorem top_sign_ne_zero [CommRing K] [Nontrivial K] (l : List (W×Bool)) : topSign (K:=K) l≠0 := by
  induction l with
  | nil => simp [topSign]
  | cons p l ih =>
    change (if p.2 then (-1:K) else 1)*(topSign (K:=K) l)≠0
    cases p.2 <;> simp [ih]

theorem violation_top_coeff [CommRing K] [Nontrivial K] (l : List (W×Bool)) :
    (violation (K:=K) l).coeff (topExponent l)=topSign (K:=K) l := by
  induction l with
  | nil => simp [violation,topExponent,topSign]
  | cons p l ih =>
    let m := Finsupp.single p.1 1 + topExponent l
    change (falseLiteral (K:=K) p * violation (K:=K) l).coeff m=(if p.2 then (-1:K) else 1)*topSign (K:=K) l
    cases hb : p.2
    · simp only [falseLiteral,hb,Bool.false_eq_true,if_false,one_mul]
      exact (MvPolynomial.coeff_X_mul _ _ _).trans ih
    · have hweight : m.sum (fun _ n=>n)=l.length+1 := exponent_weight (p::l)
      have hzero : (violation (K:=K) l).coeff m=0 :=
        MvPolynomial.coeff_eq_zero_of_totalDegree_lt (by
          change (violation (K:=K) l).totalDegree<m.sum (fun _ n=>n)
          rw [hweight]
          exact (violation_degree_le (K:=K) l).trans_lt (Nat.lt_succ_self _))
      simp only [falseLiteral,hb,if_true,sub_mul,one_mul,MvPolynomial.coeff_sub,hzero]
      rw [show m=Finsupp.single p.1 1+topExponent l from rfl,
        MvPolynomial.coeff_X_mul,ih]
      ring

theorem exponent_scope (l : List (W×Bool)) :
    (topExponent l).support=(l.map Prod.fst).toFinset := by
  induction l with
  | nil => simp [topExponent]
  | cons p l ih =>
    change (Finsupp.single p.1 1+topExponent l).support=_
    rw [List.map_cons,List.toFinset_cons,←ih]
    ext w
    by_cases h : w=p.1
    · subst w
      simp [Finsupp.mem_support_iff,Finsupp.add_apply]
    · simp [Finsupp.mem_support_iff,Finsupp.add_apply,h]

theorem violation_vars_exact [CommRing K] [Nontrivial K] (l : List (W×Bool)) :
    (violation (K:=K) l).vars=(l.map Prod.fst).toFinset := by
  apply Finset.Subset.antisymm
  · induction l with
    | nil => simp [violation]
    | cons p l ih =>
      change (falseLiteral (K:=K) p * violation (K:=K) l).vars ⊆ _
      rw [List.map_cons,List.toFinset_cons]
      apply (MvPolynomial.vars_mul _ _).trans
      have hv : (falseLiteral (K:=K) p).vars⊆{p.1} := by
        cases hb : p.2
        · simp [falseLiteral,hb,MvPolynomial.vars_X]
        · rw [falseLiteral,if_pos hb]
          have hh := MvPolynomial.vars_sub_subset (p:=(1 : MvPolynomial W K)) (q:=X p.1)
          simp only [MvPolynomial.vars_X,MvPolynomial.vars_one,Finset.empty_union] at hh
          exact hh
      intro a ha
      rcases Finset.mem_union.mp ha with ha|ha
      · exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp (hv ha)))
      · exact Finset.mem_insert_of_mem (ih ha)
  · intro w hw
    rw [←exponent_scope] at hw
    by_contra h
    have hm : topExponent l∈(violation (K:=K) l).support :=
      MvPolynomial.mem_support_iff.mpr (by rw [violation_top_coeff]; exact top_sign_ne_zero (K:=K) l)
    exact (Finsupp.mem_support_iff.mp hw) (MvPolynomial.mem_support_notMem_vars_zero hm h)

def bitValue [Zero K] [One K] (b : Bool) : K := if b then 1 else 0

theorem violation_on_bits [CommRing K] [Nontrivial K] (l : Std.Sat.CNF.Clause W) (x : W→Bool) :
    MvPolynomial.eval (bitValue (K:=K) ∘ x) (violation (K:=K) l) = if Std.Sat.CNF.Clause.eval x l then 0 else 1 := by
  induction l with
  | nil => simp [violation,Std.Sat.CNF.Clause.eval]
  | cons p l ih =>
    change MvPolynomial.eval (bitValue (K:=K) ∘ x) (falseLiteral (K:=K) p*violation (K:=K) l) =
      if (x p.1 == p.2) || Std.Sat.CNF.Clause.eval x l then 0 else 1
    rw [map_mul,ih]
    cases h₁ : p.2 <;> cases h₂ : x p.1 <;> cases h₃ : Std.Sat.CNF.Clause.eval x l <;>
      norm_num [falseLiteral,h₁,h₂,bitValue,Function.comp_apply,MvPolynomial.eval_sub]

end Polynomial

variable {V : Type*} [Fintype V]
variable (E : Finset (V×V)) (T : Finset V)

noncomputable def sparseTest (s : V→Bool) (f : CloneFactor E T) :
    MvPolynomial (Port E T) (ZMod 2) := violation (clonedClause E T s f)

theorem sparse_test_fixed_scope (s : V→Bool) (f : CloneFactor E T) :
    (sparseTest E T s f).vars = ((portList E T f).map (portOwner E T)).toFinset := by
  rw [sparseTest,violation_vars_exact,←actual_clause_ports E T s f,List.map_map]
  rfl

theorem sparse_test_degree_three (s : V→Bool) (f : CloneFactor E T) :
    (sparseTest E T s f).totalDegree≤3 :=
  (violation_degree_le _).trans (cloned_clause_width E T s f).2

theorem sparse_tests_exact (s : V→Bool) (x : Port E T→Bool) :
    (∀ f,MvPolynomial.eval (bitValue (K:=ZMod 2) ∘ x) (sparseTest E T s f)=0) ↔ (cloneCNF E T s).Sat x := by
  rw [all_cloned_clauses]
  apply forall_congr'
  intro f
  rw [sparseTest,violation_on_bits]
  cases (clonedClause E T s f).eval x <;> norm_num

#print axioms violation_degree_le
#print axioms exponent_weight
#print axioms top_sign_ne_zero
#print axioms violation_top_coeff
#print axioms exponent_scope
#print axioms violation_vars_exact
#print axioms violation_on_bits
#print axioms sparse_test_fixed_scope
#print axioms sparse_test_degree_three
#print axioms sparse_tests_exact

end Paper5.AlwaysSatOriginal.Physical