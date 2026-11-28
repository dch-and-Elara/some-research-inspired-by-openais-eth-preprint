import J6R11CollisionCost

/-!
# Deterministic exhaustive scan of the cached integer scores
-/

open scoped BigOperators Classical

namespace J6R11CollisionCostSelect
open J6R11CollisionCost

def scan {A : Type*} (v : A×ℕ) : List (A×ℕ) → A×ℕ
  | [] => v
  | w::ws => scan (if w.2 < v.2 then w else v) ws

theorem scan_in {A : Type*} (v : A×ℕ) (l : List (A×ℕ)) :
    scan v l = v ∨ scan v l ∈ l := by
  induction l generalizing v with
  | nil => exact Or.inl rfl
  | cons w ws ih =>
    simp only [scan]
    split
    · rcases ih w with h|h
      · right
        rw [h]
        exact List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · rcases ih v with h|h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)

theorem scan_min {A : Type*} (v : A×ℕ) (l : List (A×ℕ)) :
    (scan v l).2 ≤ v.2 ∧ ∀ w ∈ l, (scan v l).2 ≤ w.2 := by
  induction l generalizing v with
  | nil => simp [scan]
  | cons w ws ih =>
    simp only [scan]
    split
    next h =>
      obtain ⟨h₁,h₂⟩ := ih w
      refine ⟨h₁.trans h.le,?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl|hy
      · exact h₁
      · exact h₂ _ hy
    next h =>
      obtain ⟨h₁,h₂⟩ := ih v
      refine ⟨h₁,?_⟩
      intro y hy
      rcases List.mem_cons.mp hy with rfl|hy
      · exact h₁.trans (Nat.le_of_not_gt h)
      · exact h₂ _ hy

section Label
variable {A : Type*}

/-- Scoring once per list entry, reusing the currently best stored score. -/
def minimumEntry (score : A → ℕ) (first : A) (rest : List A) : A×ℕ :=
  let wrap (b : A) := (b,score b)
  scan (wrap first) (rest.map wrap)

theorem minimumEntry_cached (score : A → ℕ) (first : A) (rest : List A) :
    (minimumEntry score first rest).2 = score (minimumEntry score first rest).1 := by
  unfold minimumEntry
  rcases scan_in (first,score first) (rest.map fun b => (b,score b)) with h|h
  · rw [h]
  · obtain ⟨b,_,hb⟩ := List.mem_map.mp h
    rw [← hb]

theorem minimumEntry_le (score : A → ℕ) (first : A) (rest : List A) (b : A)
    (hb : b ∈ first::rest) :
    score (minimumEntry score first rest).1 ≤ score b := by
  rw [← minimumEntry_cached score first rest]
  have H := scan_min (first,score first) (rest.map fun b => (b,score b))
  rcases List.mem_cons.mp hb with rfl|hb
  · exact H.1
  · exact H.2 (b,score b) (List.mem_map.mpr ⟨b,hb,rfl⟩)

end Label

noncomputable section
variable {E R C A : Type*} [Fintype E] [Fintype R] [Fintype C] [Fintype A] [Nonempty A]

def next (row : E → R) (col : E → C) (p : R⊕C → Option A)
    (i : R⊕C) (first : A) (rest : List A) : R⊕C → Option A :=
  let S := fun b => integerScore row col (Function.update p i (some b))
  Function.update p i (some (minimumEntry S first rest).1)

theorem next_nonincreasing (row : E → R) (col : E → C) (p : R⊕C → Option A)
    (i : R⊕C) (first : A) (rest : List A) (hall : ∀ b : A, b ∈ first::rest) :
    integerScore row col (next row col p i first rest) ≤ integerScore row col p := by
  obtain ⟨b,hb⟩ := integer_greedy_step row col p i
  let S := fun b : A => integerScore row col (Function.update p i (some b))
  exact (minimumEntry_le S first rest b (hall b)).trans hb

#print axioms scan_in
#print axioms scan_min
#print axioms minimumEntry_cached
#print axioms minimumEntry_le
#print axioms next_nonincreasing

end
end J6R11CollisionCostSelect
