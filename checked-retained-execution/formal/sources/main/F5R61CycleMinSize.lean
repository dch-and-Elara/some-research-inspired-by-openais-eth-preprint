import F5R61GeneratedCycles
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Dedup

namespace F5R61
open F5R60
set_option autoImplicit false
set_option linter.unusedSimpArgs false

theorem four_distinct_members {P : Type} (L : List P) (a b c d : P)
    (once : [a,b,c,d].Nodup)
    (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ L) (hd : d ∈ L) : 4 ≤ L.length := by
  classical
  have sub : [a,b,c,d].toFinset ⊆ L.toFinset := by
    intro p present
    have m := List.mem_toFinset.mp present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with rfl|rfl|rfl|rfl
    · exact List.mem_toFinset.mpr ha
    · exact List.mem_toFinset.mpr hb
    · exact List.mem_toFinset.mpr hc
    · exact List.mem_toFinset.mpr hd
  have h := (Finset.card_le_card sub).trans (List.toFinset_card_le L)
  rw [List.toFinset_card_of_nodup once] at h
  exact h

variable {V E T : Type} [DecidableEq V] [DecidableEq T]
variable (G : RequestGraph V E T) (v : Listing V) (e : Listing E) (t : Listing T)

theorem each_actual_cycle_has_four
    (incident : ∀ x, ∃ edge, G.left edge = x ∨ G.right edge = x)
    (n : Logical V T) : 4 ≤ (actualCycleList G v e t n).length := by
  cases n with
  | inl x =>
    let L := actualCycleList G v e t (.inl x)
    have member (p : PrivatePos V E T) (eq : nameOf G p = .inl x) : p ∈ L :=
      (actualCycleList_exact_members G v e t p _).2 eq
    obtain ⟨edge,left|right⟩ := incident x
    · refine four_distinct_members L (.sw x 0) (.sw x 1) (.cf edge 0) (.er edge 0) ?_ ?_ ?_ ?_ ?_
      · simp
      · exact member _ rfl
      · exact member _ rfl
      · exact member _ (congrArg Sum.inl left)
      · exact member _ (congrArg Sum.inl left)
    · refine four_distinct_members L (.sw x 0) (.sw x 1) (.cf edge 1) (.er edge 1) ?_ ?_ ?_ ?_ ?_
      · simp
      · exact member _ rfl
      · exact member _ rfl
      · exact member _ (congrArg Sum.inl right)
      · exact member _ (congrArg Sum.inl right)
  | inr x =>
    let L := actualCycleList G v e t (.inr x)
    have member (p : PrivatePos V E T) (eq : nameOf G p = .inr x) : p ∈ L :=
      (actualCycleList_exact_members G v e t p _).2 eq
    refine four_distinct_members L (.tr x 1) (.tr x 3) (.tr x 6) (.tr x 7) ?_ ?_ ?_ ?_ ?_
    · simp
    all_goals exact member _ rfl

#print axioms four_distinct_members
#print axioms each_actual_cycle_has_four
end F5R61



