import ReceiverOrderGroupcast
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators

namespace Reconstruction.ColorAlphabet

noncomputable section

variable {T : Type*} {A : T → Type*} [Fintype T] [DecidableEq T]
  [∀ t, Fintype (A t)] [∀ t, DecidableEq (A t)]

abbrev Remaining (A : T → Type*) := ∀ t, Finset (A t)

def removeLetter (S : Remaining A) (x : Receiver A) : Remaining A :=
  Function.update S x.1 ((S x.1).erase x.2)

def Available (S : Remaining A) (v : Word A) : Prop :=
  ∀ t, (v t).1 ∈ S t ∧ (v t).2 ∈ S t

private theorem available_remove (S : Remaining A) (x : Receiver A) (v : Word A) :
    Available (removeLetter S x) v ↔ Available S v ∧ ¬ Holds x v ∧ ¬ Demands x v := by
  constructor
  · intro hv
    have ht := hv x.1
    simp only [removeLetter, Function.update_self, Finset.mem_erase] at ht
    refine ⟨fun t => ?_, ht.1.1, ht.2.1⟩
    by_cases h : t = x.1
    · subst t
      exact ⟨ht.1.2, ht.2.2⟩
    · simpa [removeLetter, Function.update_of_ne h] using hv t
  · rintro ⟨hv, hh, hd⟩ t
    by_cases h : t = x.1
    · subst t
      have ht := hv x.1
      simpa [removeLetter, ht.1, ht.2, Holds, Demands] using And.intro hh hd
    · simpa [removeLetter, Function.update_of_ne h] using hv t

def selectedWithin (S : Remaining A) (xs : List (Receiver A)) : Finset (Word A) := by
  classical
  exact Finset.univ.filter (fun v => Available S v ∧ SelectedBy xs v)

def selectedNow (S : Remaining A) (x : Receiver A) : Finset (Word A) := by
  classical
  exact Finset.univ.filter (fun v => Available S v ∧ ¬ Holds x v ∧ Demands x v)

@[simp] theorem mem_selectedWithin (S : Remaining A) (xs : List (Receiver A)) (v : Word A) :
    v ∈ selectedWithin S xs ↔ Available S v ∧ SelectedBy xs v := by
  classical
  simp [selectedWithin]

@[simp] theorem mem_selectedNow (S : Remaining A) (x : Receiver A) (v : Word A) :
    v ∈ selectedNow S x ↔ Available S v ∧ ¬ Holds x v ∧ Demands x v := by
  classical
  simp [selectedNow]

theorem selectedWithin_univ (xs : List (Receiver A)) :
    selectedWithin (fun _ => Finset.univ) xs = selectedColumns xs := by
  ext v
  simp [Available]

theorem selectedWithin_cons (S : Remaining A) (x : Receiver A) (xs : List (Receiver A)) :
    selectedWithin S (x :: xs) =
      selectedNow S x ∪ selectedWithin (removeLetter S x) xs := by
  classical
  ext v
  simp only [mem_selectedWithin, SelectedBy, Finset.mem_union, mem_selectedNow, available_remove]
  by_cases h : Demands x v <;> tauto

theorem selectedWithin_card_cons (S : Remaining A) (x : Receiver A) (xs : List (Receiver A)) :
    (selectedWithin S (x :: xs)).card =
      (selectedNow S x).card + (selectedWithin (removeLetter S x) xs).card := by
  classical
  rw [selectedWithin_cons, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro v hv hw
  have ha := ((mem_selectedNow ..).mp hv).2.2
  have hn := ((available_remove S x v).mp ((mem_selectedWithin ..).mp hw).1).2.2
  exact hn ha

private def stepPairs (S : Remaining A) (x : Receiver A) (t : T) : Finset (A t × A t) :=
  if h : t = x.1 then
    ((S t).erase (h.symm ▸ x.2)) ×ˢ ({h.symm ▸ x.2} ∩ S t)
  else S t ×ˢ S t

private theorem stepPairs_iff (S : Remaining A) (x : Receiver A) (v : Word A) :
    (∀ t, v t ∈ stepPairs S x t) ↔ Available S v ∧ ¬ Holds x v ∧ Demands x v := by
  constructor
  · intro hv
    have hx := hv x.1
    simp only [stepPairs, dite_true, Finset.mem_product, Finset.mem_erase,
      Finset.mem_inter, Finset.mem_singleton] at hx
    refine ⟨fun t => ?_, hx.1.1, hx.2.1⟩
    by_cases h : t = x.1
    · subst t
      exact ⟨hx.1.2, hx.2.2⟩
    · simpa [stepPairs, h] using hv t
  · rintro ⟨hv, hh, hd⟩ t
    by_cases h : t = x.1
    · subst t
      have ht := hv x.1
      simp only [stepPairs, dite_true, Finset.mem_product, Finset.mem_erase,
        Finset.mem_inter, Finset.mem_singleton]
      exact ⟨⟨hh, ht.1⟩, hd, ht.2⟩
    · simpa [stepPairs, h] using hv t

/-- The exact gain at a single receiver under arbitrary remaining letter sets. -/
theorem selectedNow_card (S : Remaining A) (x : Receiver A) (hx : x.2 ∈ S x.1) :
    (selectedNow S x).card = ((S x.1).card - 1) *
      ∏ i ∈ Finset.univ.erase x.1, (S i).card ^ 2 := by
  classical
  let e : ((t : T) → stepPairs S x t) ≃ {v // v ∈ selectedNow S x} :=
    { toFun := fun f => ⟨fun t => (f t).val,
        (mem_selectedNow ..).mpr ((stepPairs_iff S x _).mp fun t => (f t).property)⟩
      invFun := fun v t => ⟨v.val t, (stepPairs_iff S x _).mpr ((mem_selectedNow ..).mp v.property) t⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.card_coe, ← Fintype.card_congr e, Fintype.card_pi]
  simp only [Fintype.card_coe]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x.1)]
  congr 1
  · rw [stepPairs, dif_pos rfl, Finset.card_product, Finset.card_erase_of_mem hx,
      Finset.singleton_inter_of_mem hx, Finset.card_singleton, mul_one]
  · apply Finset.prod_congr rfl
    intro i hi
    simp [stepPairs, (Finset.mem_erase.mp hi).1, Finset.card_product, pow_two]

theorem selectedWithin_card_gain (S : Remaining A) (x : Receiver A)
    (xs : List (Receiver A)) (hx : x.2 ∈ S x.1) :
    (selectedWithin S (x :: xs)).card =
      ((S x.1).card - 1) * (∏ i ∈ Finset.univ.erase x.1, (S i).card ^ 2) +
      (selectedWithin (removeLetter S x) xs).card := by
  rw [selectedWithin_card_cons, selectedNow_card S x hx]

end

end Reconstruction.ColorAlphabet
