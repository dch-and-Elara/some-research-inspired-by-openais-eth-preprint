import J7R9Subdivision
import Mathlib.Data.Fintype.Card

/-!
# Exact size bounds for the literal compiled graph

The range is in actual physical half wires, not a count of possible
ordered lane cells or a size assumed by the contraction theorem.
-/

open Std.Sat
open scoped BigOperators

namespace J7R9Size
open J7R9Compiler J7R9Subdivision
variable {V : Type*} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
theorem occurrence_card (F : CNF V) :
    Fintype.card (Occurrence F)=∑ i : ClauseIndex F, (F.get i).length := by
  simp [Fintype.card_sigma]

theorem occurrence_partition (F : CNF V) :
    (∑ v : V, (occurrences F v).length)=Fintype.card (Occurrence F) := by
  unfold occurrences
  simp only [Finset.length_toList]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  simp

theorem wire_card (F : CNF V) :
    Fintype.card (Wire F)=Fintype.card (Occurrence F)+
      ∑ v : V, ((occurrences F v).length-3) := by
  simp [Wire,Internal,Fintype.card_sigma]

theorem half_card (F : CNF V) :
    Fintype.card (Half F)=
      2*(Fintype.card (Occurrence F)+∑ v : V, ((occurrences F v).length-3)) := by
  rw [Fintype.card_prod, Fintype.card_bool,wire_card,Nat.mul_comm]

theorem half_bounds (F : CNF V) :
    2*Fintype.card (Occurrence F)≤Fintype.card (Half F) ∧
    Fintype.card (Half F)≤4*Fintype.card (Occurrence F) := by
  have hh : (∑ v : V, ((occurrences F v).length-3))≤Fintype.card (Occurrence F) := by
    rw [← occurrence_partition F]
    exact Finset.sum_le_sum (fun _ _ => Nat.sub_le _ _)
  rw [half_card]
  omega

omit [DecidableEq V] [Fintype V] in
theorem clauses_le_occurrence (F : CNF V)
    (hn : ∀ c ∈ F, 0<c.length) :
    F.length≤Fintype.card (Occurrence F) := by
  classical
  rw [occurrence_card]
  calc
    F.length = ∑ _ : ClauseIndex F, (1:ℕ) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun i _ => hn _ (List.get_mem F i))

omit [DecidableEq V] in
theorem variables_le_occurrence (F : CNF V) (h : AllOccur F) :
    Fintype.card V ≤ Fintype.card (Occurrence F) := by
  classical
  apply Fintype.card_le_of_injective (fun v => Classical.choose (h v))
  intro u v he
  have hu := Classical.choose_spec (h u)
  have hv := Classical.choose_spec (h v)
  exact hu.symm.trans ((congrArg (fun o : Occurrence F => (literal F o).1) he).trans hv)

omit [DecidableEq V] [Fintype V] in
theorem occurrence_le_width (F : CNF V) (k : ℕ) (hk : ∀ c ∈ F, c.length≤k) :
    Fintype.card (Occurrence F) ≤ k*F.length := by
  rw [occurrence_card]
  calc
    _ ≤ ∑ _ : ClauseIndex F, k := Finset.sum_le_sum (fun i _ => hk _ (List.get_mem F i))
    _ = _ := by simp [Nat.mul_comm]

theorem source_size (F : CNF V) (k : ℕ) (h : AllOccur F)
    (hn : ∀ c ∈ F, 0<c.length) (hk : ∀ c ∈ F, c.length≤k) :
    Fintype.card V+F.length≤Fintype.card (Half F) ∧
      Fintype.card (Half F)≤4*k*F.length := by
  obtain ⟨hlo,hhi⟩ := half_bounds F
  have hV := variables_le_occurrence F h
  have hF := clauses_le_occurrence F hn
  have hk' := Nat.mul_le_mul_left 4 (occurrence_le_width F k hk)
  constructor
  · omega
  · exact hhi.trans (by simpa only [Nat.mul_assoc] using hk')

#print axioms occurrence_card
#print axioms occurrence_partition
#print axioms half_card
#print axioms half_bounds
#print axioms source_size

end J7R9Size

