import J7R9Subdivision
import J6OrientedHost
import Mathlib.Data.List.FinRange
import Mathlib.Tactic

/-!
# Source old vertices and their actual physical half-wire ports

This indexes the emitted literal clause/equality tables by their
actual finite rows and actual local port numbers. The old gate
constructor is the very one consumed by the previously verified
J6-oriented host, not an unrelated type.
-/

open Std.Sat
open scoped BigOperators

namespace J7R10Ports
open J7R9Compiler J7R9Subdivision J7R9EqualityTree

section Combinatorics
variable {A : Type*}

/-- Count actual list positions, not merely the set of their values. -/
theorem count_positions [DecidableEq A] (l : List A) (x : A) :
    l.count x = ∑ i : Fin l.length, if l.get i=x then (1:ℕ) else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    change _ = ∑ i : Fin (l.length+1), if (a::l).get i=x then (1:ℕ) else 0
    rw [Fin.sum_univ_succ]
    simp only [List.get_cons_zero,List.count_cons,beq_iff_eq]
    rw [ih]
    by_cases h : a=x <;> simp [h,eq_comm,add_comm]

theorem flatten_positions [DecidableEq A] (l : List (List A)) (x : A) :
    l.flatten.count x = ∑ i : Fin l.length, (l.get i).count x := by
  induction l with
  | nil => simp
  | cons a l ih =>
    change _ = ∑ i : Fin (l.length+1), ((a::l).get i).count x
    rw [Fin.sum_univ_succ]
    calc
      _ = List.count x a + ∑ i : Fin l.length, List.count x (l.get i) := by
        rw [List.flatten_cons,List.count_append,ih]
      _ = _ := by rfl

/-- Agreement on the actual list of a gate is the usual equality
predicate on its finite local positions, including unary/empty gates. -/
theorem agrees_of_positions (x : A → Bool) (ps : List A) :
    agrees x ps ↔ ∀ i j : Fin ps.length, x (ps.get i)=x (ps.get j) := by
  constructor
  · rintro ⟨b,hb⟩ i j
    rw [hb _ (List.get_mem _ i),hb _ (List.get_mem _ j)]
  · intro h
    cases ps with
    | nil => exact agrees_nil x
    | cons a ps =>
      refine ⟨x a,?_⟩
      intro q hq
      obtain ⟨j,hj⟩ := List.get_of_mem hq
      rw [← hj]
      exact h j ⟨0,by simp⟩

end Combinatorics

variable {V : Type*} [DecidableEq V]

abbrev TreeIndex (F : CNF V) := Σ v : V, Fin (physicalVar F v).length
abbrev Old (F : CNF V) := ClauseIndex F ⊕ TreeIndex F

noncomputable def degree (F : CNF V) : Old F → ℕ
  | .inl i => (F.get i).length
  | .inr ⟨v,g⟩ => ((physicalVar F v).get g).length

abbrev OldPort (F : CNF V) := Σ v : Old F, Fin (degree F v)

noncomputable def port (F : CNF V) : (v : Old F) → Fin (degree F v) → Half F
  | .inl i, j => (.inl ⟨i,j⟩,false)
  | .inr ⟨v,g⟩, j => ((physicalVar F v).get g).get j

noncomputable def read (F : CNF V) (q : OldPort F) : Half F := port F q.1 q.2

noncomputable def gate (F : CNF V) : (v : Old F) → J6OrientedHost.Gate (degree F v)
  | .inl i => .clause (fun j => (literal F ⟨i,j⟩).2)
  | .inr _ => .equal

theorem degree_bound (F : CNF V) (k : ℕ) (h : ∀ c ∈ F, c.length≤k)
    (v : Old F) : degree F v ≤ max k 3 := by
  rcases v with i|⟨v,g⟩
  · exact (h _ (List.get_mem _ i)).trans (le_max_left _ _)
  · exact (physical_var_degree F v _ (List.get_mem _ g)).trans (le_max_right _ _)

/-- The actual row-wise Gate.eval product is equivalent to the
compiled old-clause plus equality-tree condition. No packing
coordinates are involved at this stage. -/
theorem old_gate_evaluation (F : CNF V) (x : Half F → Bool) :
    (∀ v : Old F, (gate F v).eval (fun j => x (port F v j))=true) ↔
      physicalOldOK F x := by
  unfold physicalOldOK physicalClause
  constructor
  · intro h
    refine ⟨fun i => ?_,fun v g hg => ?_⟩
    · simpa only [gate,J6OrientedHost.Gate.eval,port,decide_eq_true_eq] using h (.inl i)
    · obtain ⟨j,rfl⟩ := List.get_of_mem hg
      apply (agrees_of_positions x _).mpr
      exact of_decide_eq_true (h (.inr ⟨v,j⟩))
  · rintro ⟨hc,hv⟩ (v|⟨v,j⟩)
    · exact decide_eq_true (hc v)
    · exact decide_eq_true ((agrees_of_positions x _).mp
        (hv v _ (List.get_mem _ j)))

#print axioms count_positions
#print axioms flatten_positions
#print axioms agrees_of_positions
#print axioms degree_bound
#print axioms old_gate_evaluation

end J7R10Ports

