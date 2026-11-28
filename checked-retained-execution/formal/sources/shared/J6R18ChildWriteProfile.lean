import J6R18ChildWriteCoeff
import A1R9Multiplicity
import Mathlib.Data.List.OfFn

/-! The exponent test reads fixed-width physical row-choice words
and computes one explicit counter per requested mode. No polynomial
coefficient, mode-frequency map or semantic equality test is a gate. -/
namespace J6R18ChildWrite
open scoped BigOperators Classical
open A1R9 AOracleMachineTime AOracleMachineTimeTape AOracleWitness
open J6PacketCoefficientBridge

def rawChoices {m : ℕ} (b : ℕ) (xs : List (Fin (m+1))) : List (List Bool) :=
  xs.map (fun j => encodeBits b j.val)

theorem rawChoices_allocation {m : ℕ} (b : ℕ) (xs : List (Fin (m+1))) :
    rawChoices b xs=allocationWords b xs.get := by
  change xs.map (fun j=>encodeBits b j.val)=
    List.ofFn ((fun j : Fin (m+1)=>encodeBits b j.val) ∘ xs.get)
  rw [← List.map_ofFn,List.ofFn_get]

theorem exp_list_as_count {m : ℕ} (xs : List (Fin (m+1))) (k : Fin m) :
    exponents (xs.map choice) k=xs.countP (fun u=>decide (choice u=some k)) := by
  induction xs with
  | nil => simp [exponents]
  | cons x xs ih =>
    simp only [List.map_cons,exponent_list_cons,Finsupp.add_apply,exponent_apply,ih]
    by_cases hx : choice x=some k <;>
      simp [hx,Nat.add_comm]

theorem exp_list_as_rows {m : ℕ} (xs : List (Fin (m+1))) (k : Fin m) :
    exponents (xs.map choice) k = rowCount xs.get k := by
  rw [exp_list_as_count,A1R9.countP_as_sum,rowCount]
  nth_rewrite 1 [← List.ofFn_get xs]
  rw [List.map_ofFn,List.sum_ofFn]
  simp only [Function.comp_apply,decide_eq_true_eq]

theorem check_profile_exact {m : ℕ} (b q : ℕ) (hq : 0<q) (hF : m+1≤2^b)
    (xs : List (Fin (m+1))) (hRows : xs.length<2^q)
    (β : Fin m→₀ℕ) (hβ : ∀ i,β i<2^q) :
    let z := checkModes q (rawChoices b xs) (counterTape b q β (List.finRange m))
    (z.result=true ↔ exponents (xs.map choice)=β) ∧
      z.steps≤m*(counterBudget xs.length b q+2) := by
  rw [rawChoices_allocation]
  have H := checkMultiplicity_exact xs.get β b q hq hF hRows hβ
  simp only [checkMultiplicity] at H
  refine ⟨H.1.trans ?_,H.2⟩
  simp only [← exp_list_as_rows]
  exact Finsupp.ext_iff.symm

#print axioms rawChoices_allocation
#print axioms exp_list_as_rows
#print axioms check_profile_exact
end J6R18ChildWrite

