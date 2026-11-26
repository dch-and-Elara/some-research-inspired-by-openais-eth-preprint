import S6Packing
import S6Cells

namespace Section6

open Finset
open scoped BigOperators
set_option linter.unusedSectionVars false

noncomputable section

variable {E V H I A : Type*} [Fintype E] [Fintype V] [DecidableEq V]
  [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I] [Fintype A] [LinearOrder A]

def placeIncidences (v : E → V) (slot : E ↪ H × WordCell I A) : H × WordCell I A → Option V :=
  fun x => if h : x ∈ Set.range slot then some (v h.choose) else none

lemma placeIncidences_at (v : E → V) (slot : E ↪ H × WordCell I A) (e : E) :
    placeIncidences v slot (slot e) = some (v e) := by
  classical
  unfold placeIncidences
  split_ifs with h
  · rw [slot.injective h.choose_spec]
  · exact False.elim (h ⟨e,rfl⟩)

def placementOfLabels (v : E → V) (first : V → I → A) (right : E → I → A)
    (copy : E → H) (hv : Function.Surjective v)
    (hc : Function.Injective (fun (e : E) => (copy e, fun i => (first (v e) i, right e i)))) :
    Placement V H I A where
  owner := placeIncidences v ⟨_, hc⟩
  first := first
  occurs := fun w => by
    obtain ⟨e, rfl⟩ := hv w
    exact ⟨_, placeIncidences_at v ⟨_, hc⟩ e⟩
  compatible := by
    classical
    intro x w hw i
    change placeIncidences v ⟨_, hc⟩ x = some w at hw
    unfold placeIncidences at hw
    split_ifs at hw with h
    · rw [← h.choose_spec]
      change first (v h.choose) i = first w i
      rw [Option.some.inj hw]

lemma occupied_eq_slot_image (v : E → V) (P : Placement V H I A)
    (slot : E ↪ H × WordCell I A) (h : P.owner = placeIncidences v slot) :
    occupied P = univ.map slot := by
  classical
  ext x
  simp only [occupied, h, mem_filter, mem_univ, true_and, mem_map]
  unfold placeIncidences
  split_ifs with hx
  · exact iff_of_true rfl (by simpa using hx)
  · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    simpa using hx

lemma loadCell_eq_fiber_card (v : E → V) (P : Placement V H I A)
    (slot : E ↪ H × WordCell I A) (h : P.owner = placeIncidences v slot) (u : WordCell I A) :
    loadCell P u = Fintype.card (cellFiber (fun e => (slot e).2) u) := by
  classical
  rw [loadCell, occupied_eq_slot_image v P slot h, filter_map, card_map, Fintype.card_subtype]
  rfl

/-- Every cell-balanced source labeling can be injected into exactly its peak
number of copies. The layout preserves the original variable labels and counts. -/
theorem realize_balanced_labels (v : E → V) (first : V → I → A) (right : E → I → A)
    (hv : Function.Surjective v)
    (hcap : ∀ u, Fintype.card (cellFiber (fun e i => (first (v e) i, right e i)) u) *
      cubeSize I A ≤ 2 * Fintype.card E) :
    ∃ h : ℕ, ∃ P : Placement V (Fin h) I A,
      P.first = first ∧
      (occupied P).card = Fintype.card E ∧
      h * cubeSize I A ≤ 2 * Fintype.card E ∧
      ∀ u, loadCell P u = Fintype.card (cellFiber (fun e i => (first (v e) i, right e i)) u) := by
  classical
  let cell (e : E) : WordCell I A := fun i => (first (v e) i,right e i)
  let h := (univ : Finset (WordCell I A)).sup (fun u => Fintype.card (cellFiber cell u))
  obtain ⟨copy, hcopy⟩ := (copies_at_peak cell).1
  let slot : E ↪ Fin h × WordCell I A := ⟨_, hcopy⟩
  let P := placementOfLabels v first right copy hv hcopy
  refine ⟨h, P, rfl, ?_, peak_copy_volume cell (Fintype.card E) hcap, ?_⟩
  · rw [occupied_eq_slot_image v P slot rfl, card_map, card_univ]
  · intro u
    exact loadCell_eq_fiber_card v P slot rfl u

#print axioms realize_balanced_labels

end
end Section6


