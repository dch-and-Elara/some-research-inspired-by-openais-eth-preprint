import J8J9GroupedCube
import J8J9GroupedBudget

/-! Exact correspondence of physical child row arguments and J9 chart rows. -/

namespace J8J9Grouped
open scoped Polynomial BigOperators Classical
open J8Physical

noncomputable section
variable {Packet R S V G : Type*} {P : V → Type*} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

-- The chart's projections can erase finiteness instances from the
-- statement even when the imported geometry proofs use them.
set_option linter.unusedSectionVars false in
omit [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V] [Fintype G]
  [(v : V) → Fintype (P v)] [(v : V) → DecidableEq (P v)] in
theorem argument_eq_chart (e : EndpointSeating d) (even : Even L) (a : S)
    (idx : Wire R ≃ Fin M) (truth : (Fin M → Bool) → Bool) (x : Cube d)
    (g : G) (r : LocalRow d g) (leg : Bool) :
    let c := J9End.chart d a idx truth
    argument d e even g (x g) r leg =
      J9FactorBounds.arg (J9FactorBounds.kernel L) (c.hit r.1 leg)
        (cubeEquiv d idx x (c.rowInput r.1 leg)) := by
  dsimp only
  change _ = J9FactorBounds.arg (J9FactorBounds.kernel L)
    (J9End.hit d (r.1,leg)) (cubeEquiv d idx x (idx (J9End.hitDestination d a (r.1,leg))))
  unfold argument
  cases hh : localHit d e even r with
  | none =>
    have hzero : J9End.hit d (r.1,leg) = false := by
      cases h : J9End.hit d (r.1,leg)
      · rfl
      · obtain ⟨y,hy⟩ := (J9End.hit_true_iff d _).1 h
        have bad := localHit_complete d e even r hy
        rw [hh] at bad
        cases bad
    simp [hzero, J9FactorBounds.arg]
  | some p =>
    by_cases hleg : p.1 = leg
    · have h := localHit_sound d e even r hh
      rw [hleg] at h
      have hs := (J9End.hit_true_iff d (r.1,leg)).2 ⟨_,h⟩
      have hbit := congrArg (fun q : Assignment d g => q.2 p.2.1 p.2.2)
        (cubeLabels_local d x g)
      change cubeLabels d x (recoverWire d p.2) = _ at hbit
      have hglob : cubeEquiv d idx x (idx (J9End.hitDestination d a (r.1,leg))) =
          (x g).2 p.2.1 p.2.2 := by
        rw [J9End.hitDestination_spec d a h]
        simpa only [cubeEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply] using hbit
      simp [hleg, hs, hglob, J9FactorBounds.arg, bit]
    · have hzero : J9End.hit d (r.1,leg) = false := by
        cases h : J9End.hit d (r.1,leg)
        · rfl
        · obtain ⟨y,hy⟩ := (J9End.hit_true_iff d _).1 h
          have bad := localHit_complete d e even r hy
          rw [hh, Option.map_some, Option.some.injEq] at bad
          exact (hleg (congrArg Prod.fst bad)).elim
      simp [hleg, hzero, J9FactorBounds.arg]

set_option linter.unusedSectionVars false in
omit [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V] [Fintype G]
  [(v : V) → Fintype (P v)] [(v : V) → DecidableEq (P v)] in
theorem target_slot_spec (a : S) (j : TargetPorts d a) (hj : j ∈ groupedTargets d a) :
    let w : Wire R := (j.1.1,j.2)
    J9End.slot d w ∈ J9End.targetSlots d a ∧
      J9End.targetWire d a (J9End.slot d w) = w := by
  dsimp only
  have htarget : (j.1.1,j.2) ∈ targets d (pinWire d a) :=
    (Finset.mem_filter.mp hj).2
  have hslot : J9End.slot d (j.1.1,j.2) ∈ J9End.targetSlots d a :=
    Finset.mem_image.mpr ⟨_,htarget,rfl⟩
  obtain ⟨hw,he⟩ := J9End.targetWire_spec d a hslot
  exact ⟨hslot,J9End.targetSlot_injective d a hw htarget he⟩

set_option linter.unusedSectionVars false in
omit [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V] [Fintype G]
  [(v : V) → Fintype (P v)] [(v : V) → DecidableEq (P v)] in
theorem groupedTarget_card (a : S) : (groupedTargets d a).card ≤ L := by
  let f : ↥(groupedTargets d a) → Fin L := fun j => J9End.slot d (j.1.1.1,j.1.2)
  have hf : Function.Injective f := by
    intro i j he
    have hi : (i.1.1.1,i.1.2) ∈ targets d (pinWire d a) := (Finset.mem_filter.mp i.2).2
    have hj : (j.1.1.1,j.1.2) ∈ targets d (pinWire d a) := (Finset.mem_filter.mp j.2).2
    have he' := J9End.targetSlot_injective d a hi hj he
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact Subtype.ext (congrArg (fun w : Wire R => w.1) he')
    · exact congrArg (fun w : Wire R => w.2) he'
  simpa using Fintype.card_le_of_injective f hf

omit [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V]
  [Fintype Packet] [DecidableEq Packet] [(v : V) → Fintype (P v)] [(v : V) → DecidableEq (P v)] in
theorem grouped_row_product (v : R → ℤ) :
    (∏ g : G, ∏ r : LocalRow d g, v r.1) = ∏ r : R, v r := by
  calc
    _ = ∏ q : (Σ g, LocalRow d g), v q.2.1 := (Fintype.prod_sigma
      (fun q : (Σ g, LocalRow d g) => v q.2.1)).symm
    _ = _ := Fintype.prod_equiv (Equiv.sigmaFiberEquiv d.rowLabel) _ _ (fun _ => rfl)

#print axioms argument_eq_chart
#print axioms target_slot_spec
#print axioms groupedTarget_card
#print axioms grouped_row_product
end
end J8J9Grouped
