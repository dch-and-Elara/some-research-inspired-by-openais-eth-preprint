import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

/-! P7 surviving-mode addresses: a Boolean subcube of actual port modes.
This counts addresses satisfying stated native filters, not distinct
nonzero observations or time needed to evaluate them. -/
namespace P7FilteredAddresses
open scoped BigOperators
variable {T : Type*} [Fintype T]

abbrev Mode (T : Type*) (d : ℕ) := T × Fin d

def exponent {d : ℕ} (bits : Mode T d → Bool) (i : Mode T d) : ℕ :=
  if bits i then 1 else 0

def cost {d : ℕ} (δ : ℕ) (bits : Mode T d → Bool) : ℕ :=
  ∑ i, (δ+i.2.val) * exponent bits i

def weight {d : ℕ} (bits : Mode T d → Bool) : ℕ :=
  ∑ i, (i.2.val+1) * exponent bits i

def order {d : ℕ} (bits : Mode T d → Bool) : ℕ := ∑ i, exponent bits i

omit [Fintype T] in
theorem exponent_injective {d : ℕ} :
    Function.Injective (exponent : (Mode T d → Bool) → Mode T d → ℕ) := by
  intro x y h
  funext i
  have e := congrFun h i
  cases hx : x i <;> cases hy : y i <;> simp_all [exponent]

theorem weight_le_cost {d : ℕ} (δ : ℕ) (hδ : 1 ≤ δ) (bits : Mode T d → Bool) :
    weight bits ≤ cost δ bits :=
  Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right _ (by omega)

theorem cost_upper {d : ℕ} (δ : ℕ) (bits : Mode T d → Bool) :
    cost δ bits ≤ Fintype.card T * (d*δ+(∑ j : Fin d, j.val)) := by
  calc
    _ ≤ ∑ i : Mode T d, (δ+i.2.val) := by
      apply Finset.sum_le_sum
      intro i _
      have h : exponent bits i ≤ 1 := by cases h : bits i <;> simp [exponent,h]
      simpa only [mul_one] using Nat.mul_le_mul_left (δ+i.2.val) h
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp [Finset.sum_add_distrib]

theorem triangular_sum (d : ℕ) : 2*(∑ j ∈ Finset.range d, j)=d*(d-1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    cases d with
    | zero => simp
    | succ d => simp; ring

/-- Joint filters for every tuple in the Boolean subcube. The input
injection assigns deliberate actual candidate rows, so allocation is
not inferred solely from a size bound. -/
theorem admissible {R : Type*} {d : ℕ} (δ p K : ℕ) (hδ : 1 ≤ δ)
    (target : Mode T d ↪ R) (eligible : Mode T d → R → Prop)
    (hrow : ∀ i, eligible i (target i))
    (hprec : Fintype.card T*(d*δ+(∑ j : Fin d, j.val))+K < p)
    (bits : Mode T d → Bool) :
    weight bits < p ∧ cost δ bits+(K-order bits) < p ∧
      ∃ allocation : {i // bits i = true} ↪ R, ∀ i, eligible i.val (allocation i) := by
  have h := cost_upper δ bits
  refine ⟨by have := weight_le_cost δ hδ bits; omega, by omega, ?_⟩
  exact ⟨(Function.Embedding.subtype _).trans target, fun i => hrow i.val⟩

theorem subcube_card {d : ℕ} :
    Nat.card (Set.range (exponent : (Mode T d → Bool) → Mode T d → ℕ)) =
      2^(Fintype.card T * d) := by
  classical
  rw [Nat.card_range_of_injective exponent_injective]
  simp [Nat.card_eq_fintype_card, Mode]

#print axioms exponent_injective
#print axioms cost_upper
#print axioms triangular_sum
#print axioms admissible
#print axioms subcube_card

end P7FilteredAddresses