import V8CapacityUnifiedHybrid
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

/-! The actual target U7 uses, not a supplied full-rank matrix. The
two-by-two OR matrix has an integral inverse, and multiplying it in
all matching coordinates gives the inverse over any coefficient ring. -/
namespace V8CapacityUnified.U7
open scoped Classical BigOperators

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1100000

variable (R : Type*) [CommRing R]

def pairOR (a b : Bool) : R := if a||b then 1 else 0

def pairInverse (a b : Bool) : R :=
  match a,b with
  | false,false => -1
  | false,true => 1
  | true,false => 1
  | true,true => 0

theorem pair_contract (a b : Bool) :
    ∑ x : Bool, pairOR R a x*pairInverse R x b=(if a=b then 1 else 0) := by
  cases a <;> cases b <;> simp [pairOR,pairInverse]

def matchingTarget (m : ℕ) : Matrix (Fin m → Bool) (Fin m → Bool) R :=
  Matrix.of fun a b => ∏ i : Fin m, pairOR R (a i) (b i)

def matchingInverse (m : ℕ) : Matrix (Fin m → Bool) (Fin m → Bool) R :=
  Matrix.of fun a b => ∏ i : Fin m, pairInverse R (a i) (b i)

theorem matching_contract (m : ℕ) :
    matchingTarget R m*matchingInverse R m=1 := by
  ext a b
  simp only [Matrix.mul_apply,matchingTarget,matchingInverse,Matrix.of_apply,
    ← Finset.prod_mul_distrib]
  let f (i : Fin m) (c : Bool) := pairOR R (a i) c*pairInverse R c (b i)
  change (∑ x : Fin m → Bool, ∏ i : Fin m, f i (x i))=_
  rw [← Fintype.prod_sum f]
  simp only [f,pair_contract]
  by_cases hab : a=b
  · subst b
    simp
  · have hh : ∃ i, a i≠b i := by
      by_contra! hn
      exact hab (funext hn)
    obtain ⟨i,hi⟩ := hh
    rw [Matrix.one_apply_ne hab]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem matching_det_ne_zero [Nontrivial R] (m : ℕ) :
    (matchingTarget R m).det≠0 := by
  have h := congrArg Matrix.det (matching_contract R m)
  rw [Matrix.det_mul,Matrix.det_one] at h
  intro h0
  rw [h0,zero_mul] at h
  exact zero_ne_one h

variable {S : Type*} [CommRing S]

theorem matching_map (f : R →+* S) (m : ℕ) :
    (matchingTarget R m).map f=matchingTarget S m := by
  ext a b
  simp only [matchingTarget,Matrix.map_apply,Matrix.of_apply,map_prod]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : a i||b i <;> simp [pairOR,h]

#print axioms pair_contract
#print axioms matching_contract
#print axioms matching_det_ne_zero
#print axioms matching_map
end
end V8CapacityUnified.U7
