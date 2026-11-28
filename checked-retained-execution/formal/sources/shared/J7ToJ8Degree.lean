import J7ToJ8Incidence
import J7SeatMatching

/-! # Actual physical nonpin conflict degree from the typed incidences -/
open scoped BigOperators Classical

namespace J7ToJ8Degree
open J7SourceLabels J7SeatSource J7SeatMatching J7ToJ8Incidence

noncomputable section

private theorem fiber_count {X Y : Type*} [Fintype X] (f : X → Y) (y : Y) :
    (Finset.univ.filter fun x => f x = y).card = Nat.card {x // f x = y} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- On the physical nonpin graph the closed conflict neighbourhood has
size at most five: at most two legs at the subdivision and at most three
at its actual old column. No random-label independence is needed here. -/
theorem physical_degree_le_five {Pair Row Col W : Type*} [Fintype Pair] [Fintype W]
    (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (two : ∀ v, Nat.card {w : W // row w = v} = 2)
    (clone_cap : ∀ p : Pin Pair, (Finset.univ.filter fun w : W => col w = Sum.inl p).card ≤ 2)
    (col_cap : ∀ c, (Finset.univ.filter fun w : W => col w = Sum.inr c).card ≤ 3) :
    ∀ (w : {w // nonpin col w}),
      (nearby (fun e => rowNode row e.val) (fun e => colNode col e.val) w).card ≤ 5 := by
  classical
  let E := {w : Wire Pair W // nonpin col w}
  change ∀ w : E, (nearby (fun e : E => rowNode row e.val) (fun e : E => colNode col e.val) w).card ≤ 2+3
  apply degree_from_owners
  · intro v
    rw [fiber_count]
    let f : {e : E // rowNode row e.val = v} ↪ {e : Wire Pair W // rowNode row e = v} :=
      ⟨fun e => ⟨e.val.val,e.prop⟩,fun _ _ h => Subtype.ext (Subtype.ext
        (congrArg (fun q : {e : Wire Pair W // rowNode row e = v} => q.val) h))⟩
    have hs := Nat.card_le_card_of_injective f f.injective
    rwa [Nat.card_congr (rowFiber row two v), Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at hs
  · intro v
    rw [fiber_count]
    cases v with
    | inl p =>
      letI : IsEmpty {e : E // colNode col e.val = Sum.inl p} :=
        ⟨fun e => by
          obtain ⟨c,hc⟩ := e.val.prop
          exact Sum.noConfusion (e.prop.symm.trans hc)⟩
      rw [Nat.card_eq_fintype_card, Fintype.card_of_isEmpty]; exact Nat.zero_le _
    | inr v =>
      let f : {e : E // colNode col e.val = Sum.inr v} ↪ Ports col v :=
        ⟨fun e => ⟨e.val.val,e.prop⟩,fun _ _ h => Subtype.ext (Subtype.ext
          (congrArg (fun q : Ports col v => q.val) h))⟩
      refine (Nat.card_le_card_of_injective f f.injective).trans ?_
      cases v with
      | inl p =>
        rw [Nat.card_congr (clonePorts col p), Nat.card_sum, Nat.card_eq_fintype_card (α := Unit),
          Fintype.card_unit, ← fiber_count]
        have he : (Finset.univ.filter fun w : W => col w = Sum.inl p).card ≤ 2 := clone_cap p
        have hq : 1 + (Finset.univ.filter fun w : W => col w = Sum.inl p).card ≤ 3 :=
          Nat.add_le_add_left he 1
        convert hq using 1
        congr 2
        exact Finset.ext fun w => by simp only [Finset.mem_filter]
      | inr v =>
        rw [Nat.card_congr (ordinaryPorts col v), ← fiber_count]
        convert col_cap v using 1
        congr 1
        exact Finset.ext fun w => by simp only [Finset.mem_filter]

#print axioms physical_degree_le_five

end
end J7ToJ8Degree
