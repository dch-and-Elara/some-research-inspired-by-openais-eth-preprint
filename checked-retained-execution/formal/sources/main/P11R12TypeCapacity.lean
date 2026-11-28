import P11R12Coverage

namespace P11R12TypeCapacity
open scoped Classical BigOperators
open P11FullPacking P11R12Choice P11R12Coverage OuterNodePacking
variable {K W : Type*} [LinearOrder K] [Fintype W] {a b : ℕ}

noncomputable def typeCells (k : Key (Fin a) K) [Fintype (Orient k)] : Finset (Cell (Fin a) K) :=
  Finset.univ.image (cell k)

theorem mem_typeCells (k : Key (Fin a) K) [Fintype (Orient k)] (c : Cell (Fin a) K) :
    c ∈ typeCells k ↔ key c = k := by
  classical
  constructor
  · intro h
    obtain ⟨o,_,rfl⟩ := Finset.mem_image.mp h
    exact key_cell k o
  · intro hk
    subst k
    exact Finset.mem_image.mpr ⟨orientation c,Finset.mem_univ _,cell_decode c⟩

theorem typeCells_card (k : Key (Fin a) K) [Fintype (Orient k)] :
    (typeCells k).card = Fintype.card (Orient k) := by
  classical
  unfold typeCells
  rw [Finset.card_image_of_injective _ (cell_injective k),Finset.card_univ]

/-- Counting actual legs, regardless of their later cell permutation: the
unordered type load is bounded by the number of its ordered orientations
times the maximum actual ordered-cell load. -/
theorem typeLoad_le_orientations (f : W → Cell (Fin a) K)
    (k : Key (Fin a) K) [Fintype (Orient k)] (m : ℕ)
    (hload : ∀ c, ((Finset.univ : Finset W).filter (fun w => f w=c)).card ≤ m) :
    typeLoad f k ≤ Fintype.card (Orient k)*m := by
  classical
  let U := (Finset.univ : Finset W).filter (fun w => key (f w)=k)
  have htarget : ∀ w ∈ U, f w ∈ typeCells k := by
    intro w hw
    exact (mem_typeCells k (f w)).mpr (Finset.mem_filter.mp hw).2
  change U.card ≤ _
  rw [Finset.card_eq_sum_card_fiberwise htarget]
  calc
    _ ≤ ∑ _c ∈ typeCells k, m := by
      apply Finset.sum_le_sum
      intro c _
      apply le_trans _ (hload c)
      apply Finset.card_le_card
      intro w hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ w,(Finset.mem_filter.mp hw).2⟩
    _ = _ := by simp [typeCells_card]

/-- The actual P11 picked set inherits this cap, with no separate hQ. -/
theorem actual_pick_cap (ω : Draw a b K) (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a)
    (side : W → Bool) (k : Key (Fin a) K) [Fintype (Orient k)] (m : ℕ)
    (hload : ∀ c, ((Finset.univ : Finset W).filter (fun w => f w=c)).card ≤ m) :
    (picked ω f cap side k).card ≤ Fintype.card (Orient k)*m :=
  (picked_le_typeLoad ω f cap side k).trans (typeLoad_le_orientations f k m hload)

#print axioms mem_typeCells
#print axioms typeCells_card
#print axioms typeLoad_le_orientations
#print axioms actual_pick_cap
end P11R12TypeCapacity
