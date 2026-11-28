import Mathlib.Tactic
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.Rat.Lemmas

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

/-! Integer coefficient l¹ norm, including the literal polynomial
truncation used for MAIN's rational Taylor register. -/
namespace V8NativeMessage.N1
open scoped Classical BigOperators Polynomial
open Polynomial
noncomputable section

def coeffNorm (p : ℤ[X]) : ℕ := ∑ j ∈ p.support, (p.coeff j).natAbs

theorem norm_over {p : ℤ[X]} {s : Finset ℕ} (hs : p.support ⊆ s) :
    coeffNorm p = ∑ j ∈ s, (p.coeff j).natAbs := by
  apply Finset.sum_subset hs
  intro j _ h
  simp [Polynomial.notMem_support_iff.mp h]

@[simp] theorem norm_zero : coeffNorm 0=0 := by simp [coeffNorm]

@[simp] theorem norm_monomial (j : ℕ) (a : ℤ) :
    coeffNorm (monomial j a)=a.natAbs := by
  rw [norm_over (support_monomial' j a)]
  simp

@[simp] theorem norm_C (a : ℤ) : coeffNorm (C a)=a.natAbs := by
  rw [← monomial_zero_left, norm_monomial]

@[simp] theorem norm_one : coeffNorm 1=1 := by
  simpa only [map_one,Int.natAbs_one] using norm_C (1:ℤ)

@[simp] theorem norm_X : coeffNorm X=1 := by
  simpa only [monomial_one_one_eq_X,Int.natAbs_one] using norm_monomial 1 (1:ℤ)

@[simp] theorem norm_neg (p : ℤ[X]) : coeffNorm (-p)=coeffNorm p := by
  simp [coeffNorm]

theorem norm_add (p q : ℤ[X]) : coeffNorm (p+q)≤coeffNorm p+coeffNorm q := by
  classical
  rw [norm_over (support_add (p:=p) (q:=q)),
    norm_over (Finset.subset_union_left : p.support⊆p.support∪q.support),
    norm_over (Finset.subset_union_right : q.support⊆p.support∪q.support),
    ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun _ _ => by simpa only [coeff_add] using Int.natAbs_add_le _ _)

theorem norm_sub (p q : ℤ[X]) : coeffNorm (p-q)≤coeffNorm p+coeffNorm q := by
  simpa only [sub_eq_add_neg,norm_neg] using norm_add p (-q)

theorem norm_sum {I : Type*} (s : Finset I) (f : I→ℤ[X]) :
    coeffNorm (∑ i ∈ s, f i)≤∑ i ∈ s, coeffNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (norm_add _ _).trans (Nat.add_le_add_left ih _)

theorem norm_mul (p q : ℤ[X]) : coeffNorm (p*q)≤coeffNorm p*coeffNorm q := by
  have hp : p*q = ∑ i ∈ p.support, ∑ j ∈ q.support,
      monomial (i+j) (p.coeff i*q.coeff j) := by
    conv_lhs => rw [p.as_sum_support,q.as_sum_support,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [Finset.mul_sum, monomial_mul_monomial]
  rw [hp]
  calc
    _ ≤ ∑ i ∈ p.support, coeffNorm (∑ j ∈ q.support,
        monomial (i+j) (p.coeff i*q.coeff j)) := norm_sum _ _
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support, (p.coeff i).natAbs*(q.coeff j).natAbs := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [norm_monomial,Int.natAbs_mul] using norm_sum q.support
        (fun j => monomial (i+j) (p.coeff i*q.coeff j))
    _ = coeffNorm p*coeffNorm q := by
      simp only [coeffNorm,Finset.sum_mul,Finset.mul_sum]; exact Finset.sum_comm

theorem norm_prod {I : Type*} (s : Finset I) (f : I→ℤ[X]) :
    coeffNorm (∏ i ∈ s, f i)≤∏ i ∈ s, coeffNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi]
    exact (norm_mul _ _).trans (Nat.mul_le_mul_left _ ih)

theorem norm_pow (p : ℤ[X]) (n : ℕ) : coeffNorm (p^n)≤coeffNorm p^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,pow_succ]
    exact (norm_mul _ _).trans (Nat.mul_le_mul_right _ ih)

theorem norm_bound_degree (p : ℤ[X]) (R B : ℕ) (hR : p.natDegree≤R)
    (hB : ∀ j, (p.coeff j).natAbs ≤ B) : coeffNorm p≤(R+1)*B := by
  rw [norm_over (p:=p) (s:=Finset.range (R+1)) (fun j hj =>
    Finset.mem_range.mpr (Nat.lt_succ_of_le ((le_natDegree_of_mem_supp j hj).trans hR)))]
  calc
    _ ≤ ∑ j ∈ Finset.range (R+1), B := Finset.sum_le_sum fun j _ => hB j
    _ = _ := by simp

theorem coeff_le_norm (p : ℤ[X]) (j : ℕ) : (p.coeff j).natAbs≤coeffNorm p := by
  by_cases h : j∈p.support
  · unfold coeffNorm
    exact Finset.single_le_sum (f:=fun n => (p.coeff n).natAbs) (fun _ _ => Nat.zero_le _) h
  · simp [Polynomial.notMem_support_iff.mp h]

theorem norm_comp (p q : ℤ[X]) (R B : ℕ) (hR : p.natDegree≤R)
    (hq : coeffNorm q≤B) (hB : 0<B) : coeffNorm (p.comp q)≤coeffNorm p*B^R := by
  have hp : p.comp q = ∑ i ∈ p.support, C (p.coeff i) * q^i := by
    conv_lhs => rw [p.as_sum_support_C_mul_X_pow]
    change compRingHom q (∑ i ∈ p.support, C (p.coeff i) * X^i)=_
    simp only [map_sum,coe_compRingHom_apply,mul_comp,C_comp,pow_comp,X_comp]
  rw [hp]
  calc
    _ ≤ ∑ i ∈ p.support, coeffNorm (C (p.coeff i)*q^i) := norm_sum _ _
    _ ≤ ∑ i ∈ p.support, (p.coeff i).natAbs*B^R := by
      apply Finset.sum_le_sum
      intro i hi
      apply (norm_mul _ _).trans
      rw [norm_C]
      apply Nat.mul_le_mul_left
      exact (norm_pow _ _).trans
        ((Nat.pow_le_pow_left hq _).trans (Nat.pow_le_pow_right hB
          ((le_natDegree_of_mem_supp i hi).trans hR)))
    _ = _ := by rw [coeffNorm,Finset.sum_mul]

theorem norm_eval (p : ℤ[X]) (t : ℤ) (R B : ℕ) (hR : p.natDegree≤R)
    (ht : t.natAbs≤B) (hB : 0<B) : (p.eval t).natAbs≤coeffNorm p*B^R := by
  simpa only [comp_C,norm_C] using norm_comp p (C t) R B hR (by simpa only [norm_C]) hB

#print axioms norm_add
#print axioms norm_sub
#print axioms norm_mul
#print axioms norm_prod
#print axioms norm_bound_degree
#print axioms coeff_le_norm
#print axioms norm_comp
#print axioms norm_eval
end
end V8NativeMessage.N1
