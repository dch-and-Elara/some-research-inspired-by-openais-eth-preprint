import P5NativeEntryFixing
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.MvPolynomial.Eval

/-! At a full test-list call the *actual* source polynomials are affine.
The high-incidence branch that fixes the pins correctly removes exactly its
zero constant rows, without introducing a contradictory constant. -/
namespace Paper5.NativeEntry
open scoped BigOperators
open MvPolynomial

noncomputable def affine {V : Type*} [Fintype V] (s r : V → F₂) : MvPolynomial V F₂ :=
  C (∑ v,r v*s v)+∑ v,C (r v)*X v

theorem affine_evaluate {V : Type*} [Fintype V] (s r x : V → F₂) :
    MvPolynomial.eval x (affine s r)=∑ v,r v*(x v+s v) := by
  simp [affine,mul_add,Finset.sum_add_distrib,add_comm]

theorem affine_vars {V : Type*} [Fintype V] [DecidableEq V] (s r : V → F₂) :
    (affine s r).vars=Finset.univ.filter (fun v=>r v≠0) := by
  have hv (v : V) : (C (r v)*X v : MvPolynomial V F₂).vars =
      if r v=0 then ∅ else {v} := by
    by_cases he : r v=0
    · simp [he]
    · rw [if_neg he,vars_C_mul _ he,vars_X]
  have hd : Pairwise (fun i j : V=>
      Disjoint (C (r i)*X i : MvPolynomial V F₂).vars
        (C (r j)*X j : MvPolynomial V F₂).vars) := by
    intro i j h
    rw [hv,hv]
    split_ifs <;> simp_all [Ne.symm h]
  unfold affine
  rw [vars_add_of_disjoint (by simp only [vars_C,Finset.disjoint_empty_left]),vars_C,Finset.empty_union,
    vars_sum_of_disjoint Finset.univ _ hd]
  ext v
  simp only [Finset.mem_biUnion,Finset.mem_filter,Finset.mem_univ,true_and,hv]
  constructor
  · rintro ⟨i,hi⟩
    split_ifs at hi with h
    · simp at hi
    · simpa only [Finset.mem_singleton.mp hi] using h
  · intro h
    exact ⟨v,by simp [h]⟩

noncomputable def sourcePolynomial {n : ℕ} (r : Word n) (sgn : Fin n → Bool) : MvPolynomial (Fin n) F₂ :=
  ∑ v,C (r v)*(if sgn v then 1+X v else X v)

theorem source_polynomial_affine {n : ℕ} (r : Word n) (sgn : Fin n → Bool) :
    sourcePolynomial r sgn = affine (fun v=>asBit (sgn v)) r := by
  unfold sourcePolynomial affine
  simp only [map_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  cases sgn v
  · simp [asBit]
  · simp only [asBit,if_true,mul_one]
    ring

theorem source_polynomial_eval {n : ℕ} (r : Word n) (sgn x : Fin n→Bool) :
    MvPolynomial.eval (fun v=>asBit (x v)) (sourcePolynomial r sgn)=sourceTest r sgn x := by
  rw [source_polynomial_affine,affine_evaluate,source_test_formula,rowForm_apply]
  rfl

theorem source_polynomial_scope {n : ℕ} (r : Word n) (sgn : Fin n→Bool) :
    (sourcePolynomial r sgn).vars=support r := by
  rw [source_polynomial_affine,affine_vars,support]

noncomputable def consistentSubst {n : ℕ} (A : Rows n) (sgn : Fin n→Bool) (v : Fin n) :
    MvPolynomial (Free A) F₂ :=
  if h : v∈(fixed A)ᶜ then X (⟨v,h⟩ : Free A) else C (asBit (sgn v))

noncomputable def branchPolynomial {n : ℕ} (A : Rows n) (r : Word n) (sgn : Fin n→Bool) :
    MvPolynomial (Free A) F₂ :=
  affine (fun v=>asBit (sgn v)) (fun v=>r v)

theorem two_bits_cancel (b : Bool) : asBit b+asBit b=0 := by
  cases b <;> decide

theorem polynomial_after_fixing {n : ℕ} (A : Rows n) (r : Word n) (sgn : Fin n→Bool) :
    eval₂Hom C (consistentSubst A sgn) (sourcePolynomial r sgn)=
      branchPolynomial A r sgn := by
  classical
  have step (v : Fin n) :
      eval₂Hom C (consistentSubst A sgn) (C (r v)*(if sgn v then 1+X v else X v)) =
      (if h : v∈(fixed A)ᶜ then
        C (r v)*(C (asBit (sgn v))+X (⟨v,h⟩ : Free A)) else 0) := by
    have hx : (if sgn v then 1+(X v : MvPolynomial (Fin n) F₂) else X v)
        =C (asBit (sgn v))+X v := by cases sgn v <;> simp [asBit]
    rw [hx,map_mul,eval₂Hom_C,map_add,eval₂Hom_C,eval₂Hom_X']
    unfold consistentSubst
    split_ifs with hv
    · rfl
    · rw [←map_add,two_bits_cancel,map_zero,mul_zero]
  unfold sourcePolynomial
  rw [map_sum]
  simp only [step]
  change ∑ v : Fin n,(if h : v∈(fixed A)ᶜ then
      (C (r v)*(C (asBit (sgn v))+X (⟨v,h⟩ : Free A))) else 0)=_
  have hs := Finset.sum_attach_eq_sum_dite ((fixed A)ᶜ)
    (fun v : Free A=>C (r v)*(C (asBit (sgn v))+X v))
  rw [←hs,←Finset.univ_eq_attach]
  unfold branchPolynomial affine
  simp only [mul_add,←map_mul,Finset.sum_add_distrib,map_sum]

theorem branch_polynomial_scope {n : ℕ} (A : Rows n) (r : Word n) (sgn : Fin n→Bool) :
    (branchPolynomial A r sgn).vars=restrictedSupport A r := by
  rw [branchPolynomial,affine_vars,restrictedSupport]

theorem branch_zero_if_no_variables {n : ℕ} (A : Rows n) (r : Word n) (sgn : Fin n→Bool)
    (h : restrictedSupport A r=∅) : branchPolynomial A r sgn=0 := by
  have hh (v : Free A) : r v=0 := by
    by_contra H
    have hf := (mem_restricted_support A r v).mpr H
    simp [h] at hf
  simp [branchPolynomial,affine,hh]

theorem constant_rows_exactly_zero_when_removed {n : ℕ} (A : Rows n)
    (sgn : Fin n→Bool) (i : Fin A.length) :
    i∉retained A ↔ branchPolynomial A (A.get i) sgn=0 := by
  simp only [retained,Finset.mem_filter,Finset.mem_univ,true_and,Finset.not_nonempty_iff_eq_empty]
  constructor
  · exact branch_zero_if_no_variables A _ sgn
  · intro h
    rw [←branch_polynomial_scope A _ sgn,h,vars_0]

#print axioms affine_evaluate
#print axioms affine_vars
#print axioms source_polynomial_affine
#print axioms source_polynomial_eval
#print axioms source_polynomial_scope
#print axioms two_bits_cancel
#print axioms polynomial_after_fixing
#print axioms branch_polynomial_scope
#print axioms branch_zero_if_no_variables
#print axioms constant_rows_exactly_zero_when_removed
end Paper5.NativeEntry