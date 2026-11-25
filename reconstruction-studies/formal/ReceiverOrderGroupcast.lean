import ColorAlphabetModel
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup

namespace Reconstruction.ColorAlphabet

variable {T : Type*} {A : T → Type*}

/-- A column is selected if some first demand comes strictly before the first holder.
A receiver holding its own demand counts as a holder at that position. -/
def SelectedBy : List (Receiver A) → Word A → Prop
  | [], _ => False
  | x :: xs, v => ¬ Holds x v ∧ (Demands x v ∨ SelectedBy xs v)

private theorem selected_append {xs : List (Receiver A)} {v : Word A}
    (h : SelectedBy xs v) (ys : List (Receiver A)) : SelectedBy (xs ++ ys) v := by
  induction xs with
  | nil => exact False.elim h
  | cons x xs ih =>
      exact ⟨h.1, h.2.imp_right ih⟩

theorem generalizedIndependent_of_order {xs : List (Receiver A)} {S : Finset (Word A)}
    (hS : ∀ u ∈ S, SelectedBy xs u) : GeneralizedIndependent S := by
  classical
  intro U hU hn
  have h : ∀ u ∈ U, SelectedBy xs u := fun u hu => hS u (hU hu)
  clear hS hU S
  induction xs with
  | nil =>
      obtain ⟨u, hu⟩ := hn
      exact False.elim (h u hu)
  | cons x xs ih =>
      by_cases hx : ∃ u ∈ U, Demands x u
      · exact ⟨x, hx, fun v hv => (h v hv).1⟩
      · apply ih
        intro u hu
        exact (h u hu).2.resolve_left fun hd => hx ⟨u, hu, hd⟩

private theorem independent_has_prefix (S : Finset (Word A)) (hS : GeneralizedIndependent S) :
    ∃ xs : List (Receiver A), xs.Nodup ∧
      (∀ u ∈ S, SelectedBy xs u) ∧ ∀ x ∈ xs, ∃ u ∈ S, Demands x u := by
  classical
  induction S using Finset.strongInductionOn
  rename_i S ih
  by_cases hS0 : S.Nonempty
  · obtain ⟨x, ⟨u, hu, hux⟩, hx⟩ := hS S (by rfl) hS0
    let U := S.filter (fun v => ¬ Demands x v)
    have hUS : U ⊆ S := Finset.filter_subset _ _
    have hlt : U ⊂ S := Finset.ssubset_iff_subset_ne.mpr ⟨hUS, by
      intro he
      have huU : u ∈ U := he.symm ▸ hu
      change u ∈ S.filter (fun v => ¬ Demands x v) at huU
      exact (Finset.mem_filter.mp huU).2 hux⟩
    obtain ⟨xs, hnd, htail, hmem⟩ := ih U hlt
      (fun V hV hV0 => hS V (hV.trans hUS) hV0)
    have hnx : x ∉ xs := by
      intro hm
      obtain ⟨v, hv, hvx⟩ := hmem x hm
      exact (Finset.mem_filter.mp hv).2 hvx
    refine ⟨x :: xs, List.nodup_cons.mpr ⟨hnx, hnd⟩, ?_, ?_⟩
    · intro v hv
      refine ⟨hx v hv, or_iff_not_imp_left.mpr ?_⟩
      exact fun h => htail v (Finset.mem_filter.mpr ⟨hv, h⟩)
    · intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨u, hu, hux⟩
      · obtain ⟨v, hv, hvy⟩ := hmem y hy
        exact ⟨v, hUS hv, hvy⟩
  · refine ⟨[], by simp, fun u hu => False.elim (hS0 ⟨u, hu⟩), by simp⟩

variable [Fintype T] [DecidableEq T] [∀ t, Fintype (A t)] [∀ t, DecidableEq (A t)]

/-- All labelled permutations of the receivers, represented by duplicate-free exhaustive lists. -/
def CompleteOrder (xs : List (Receiver A)) : Prop :=
  xs.Nodup ∧ ∀ x : Receiver A, x ∈ xs

/-- Exactly the selected groupcast columns under a given receiver order. -/
noncomputable def selectedColumns (xs : List (Receiver A)) : Finset (Word A) := by
  classical
  exact Finset.univ.filter (SelectedBy xs)

omit [∀ t, DecidableEq (A t)] in
@[simp] theorem mem_selectedColumns (xs : List (Receiver A)) (u : Word A) :
    u ∈ selectedColumns xs ↔ SelectedBy xs u := by
  classical
  simp [selectedColumns]

/-- Generalized independence in this unit-message groupcast model is equivalent to
being included among the columns of some complete labelled receiver order. -/
theorem generalizedIndependent_iff_order (S : Finset (Word A)) :
    GeneralizedIndependent S ↔
      ∃ xs : List (Receiver A), CompleteOrder xs ∧ S ⊆ selectedColumns xs := by
  classical
  refine ⟨fun h => ?_, fun ⟨xs, _, hs⟩ => ?_⟩
  · obtain ⟨xs, hnd, hsel, _⟩ := independent_has_prefix S h
    let rem := Finset.univ.filter (fun x : Receiver A => x ∉ xs)
    refine ⟨xs ++ rem.toList, ⟨?_, ?_⟩, ?_⟩
    · refine List.nodup_append'.mpr ⟨hnd, rem.nodup_toList, ?_⟩
      rw [List.disjoint_iff_ne]
      intro x hx y hy hxy
      subst y
      exact (Finset.mem_filter.mp (Finset.mem_toList.mp hy)).2 hx
    · intro x
      by_cases hx : x ∈ xs
      · exact List.mem_append_left _ hx
      · exact List.mem_append_right _ (Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩))
    · intro v hv
      exact (mem_selectedColumns ..).mpr (selected_append (hsel v hv) _)
  · exact generalizedIndependent_of_order (fun u hu => (mem_selectedColumns ..).mp (hs hu))

/-- The two extremal problems have the same upper bounds. This includes redundant
self-held requests because such a request can never witness independence or selection. -/
theorem orders_bound_iff_generalizedIndependence_bound (n : ℕ) :
    (∀ xs : List (Receiver A), CompleteOrder xs → (selectedColumns xs).card ≤ n) ↔
    (∀ S : Finset (Word A), GeneralizedIndependent S → S.card ≤ n) := by
  refine ⟨fun h S hS => ?_, fun h xs _ => ?_⟩
  · obtain ⟨xs, hx, hs⟩ := (generalizedIndependent_iff_order S).mp hS
    exact (Finset.card_le_card hs).trans (h xs hx)
  · exact h _ (generalizedIndependent_of_order (fun v hv => (mem_selectedColumns ..).mp hv))

end Reconstruction.ColorAlphabet
