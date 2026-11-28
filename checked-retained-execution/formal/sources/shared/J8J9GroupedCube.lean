import J8J9GroupedPhysical
import J9EndMoment

/-! The grouped assignment cube is the unduplicated global physical cube;
the grouped feature is exactly the corresponding physical tile moment. -/

namespace J8J9Grouped
open scoped Polynomial BigOperators Classical
open J8Physical

noncomputable section
variable {Packet R S V G : Type*} {P : V → Type*} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

abbrev Assignment (g : G) := (LocalPin d g → Bool) × LocalBits d g
abbrev Cube := (g : G) → Assignment d g

def localLabels (g : G) (x : Wire R → Bool) : Assignment d g :=
  ((fun p => x (pinWire d p.1)), fun v q => x (ordinaryWire d ⟨v.1,q⟩))

def cubeLabels (x : Cube d) (w : Wire R) : Bool :=
  match d.column w with
  | Sum.inl p => (x (d.pinLabel p)).1 ⟨p,rfl⟩
  | Sum.inr ⟨v,q⟩ => (x (d.colLabel v)).2 ⟨v,rfl⟩ q

omit [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V]
  [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
  [(v : V) → Fintype (P v)] [(v : V) → DecidableEq (P v)] in
theorem cubeLabels_pin (x : Cube d) (p : S) :
    cubeLabels d x (pinWire d p) = (x (d.pinLabel p)).1 ⟨p,rfl⟩ := by
  unfold cubeLabels pinWire
  rw [d.column.apply_symm_apply]

omit [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V]
  [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
  [(v : V) → Fintype (P v)] [(v : V) → DecidableEq (P v)] in
theorem cubeLabels_old (x : Cube d) (p : Sigma P) :
    cubeLabels d x (ordinaryWire d p) = (x (d.colLabel p.1)).2 ⟨p.1,rfl⟩ p.2 := by
  unfold cubeLabels ordinaryWire
  rw [d.column.apply_symm_apply]

omit [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V]
  [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
  [(v : V) → Fintype (P v)] [(v : V) → DecidableEq (P v)] in
theorem cubeLabels_local (x : Cube d) (g : G) : localLabels d g (cubeLabels d x) = x g := by
  apply Prod.ext
  · funext p
    obtain ⟨p,hp⟩ := p
    subst g
    exact cubeLabels_pin d x p
  · funext v q
    obtain ⟨v,hv⟩ := v
    subst g
    exact cubeLabels_old d x ⟨v,q⟩

omit [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype V] [DecidableEq V]
  [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
  [(v : V) → Fintype (P v)] [(v : V) → DecidableEq (P v)] in
theorem localLabels_cube (x : Wire R → Bool) (w : Wire R) :
    cubeLabels d (fun g => localLabels d g x) w = x w := by
  unfold cubeLabels
  generalize hw : d.column w = p
  have he : d.column.symm p = w := by rw [← hw, d.column.symm_apply_apply]
  cases p with
  | inl p =>
    change x (pinWire d p) = x w
    rw [show pinWire d p = w from he]
  | inr p =>
    obtain ⟨v,q⟩ := p
    change x (ordinaryWire d ⟨v,q⟩) = x w
    rw [show ordinaryWire d ⟨v,q⟩ = w from he]

def cubeEquiv (idx : Wire R ≃ Fin M) : Cube d ≃ (Fin M → Bool) where
  toFun x i := cubeLabels d x (idx.symm i)
  invFun x g := localLabels d g (x ∘ idx)
  left_inv x := by
    funext g
    change localLabels d g ((fun i => cubeLabels d x (idx.symm i)) ∘ idx) = x g
    simp only [Function.comp_def, Equiv.symm_apply_apply]
    exact cubeLabels_local d x g
  right_inv x := by
    funext i
    change cubeLabels d (fun g => localLabels d g (x ∘ idx)) (idx.symm i) = x i
    rw [localLabels_cube, Function.comp_apply, Equiv.apply_symm_apply]

omit [Fintype R] [DecidableEq R] [Fintype Packet] [DecidableEq Packet] in
theorem cube_card (idx : Wire R ≃ Fin M) : Fintype.card (Cube d) = 2^M := by
  rw [Fintype.card_congr (cubeEquiv d idx)]
  simp

-- Projection to the moment erases the chart's proof-time packet enumeration;
-- the imported chart identification still needs that finite instance.
set_option linter.unusedSectionVars false in
omit [DecidableEq S] [DecidableEq V] [Fintype G] [(v : V) → DecidableEq (P v)] in
theorem cubeFeature_eq (a : S) (b : Fin (Fintype.card (PinTile d a)))
    (idx : Wire R ≃ Fin M) (truth : (Fin M → Bool) → Bool) (x : Cube d) :
    feature d a b (x (d.pinLabel a)) =
      J9FactorBounds.moment (J9End.chart d a idx truth) b (cubeEquiv d idx x) := by
  rw [J9End.chart_moment_pin_old]
  unfold feature bit
  push_cast
  rw [add_comm]
  congr 1
  · rw [Fintype.sum_equiv (pinEnumeration d a) _ (fun p =>
        (if (x (d.pinLabel a)).1 (tilePinInSource d p) then (1:ℤ) else 0) *
          (ordinal d (pinWire d p.1) : ℤ)^(b:ℕ)) (fun _ => rfl)]
    apply Finset.sum_congr rfl
    intro q hq
    have h := congrArg (fun y : Assignment d (d.pinLabel a) =>
      y.1 (tilePinInSource d q)) (cubeLabels_local d x (d.pinLabel a))
    change cubeLabels d x (pinWire d q.1) = _ at h
    simp only [cubeEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply, h, mul_comm]
  · apply Finset.sum_congr rfl
    intro q hq
    have h := congrArg (fun y : Assignment d (d.pinLabel a) =>
      y.2 (tileOldInSource d q).1 (tileOldInSource d q).2)
      (cubeLabels_local d x (d.pinLabel a))
    change cubeLabels d x (ordinaryWire d q.1) = _ at h
    simp only [cubeEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply, h]

set_option linter.unusedSectionVars false in
omit [DecidableEq S] [DecidableEq V] [Fintype G] [(v : V) → DecidableEq (P v)] in
theorem cubeFeature_bound (a : S) (b : Fin (Fintype.card (PinTile d a)))
    (idx : Wire R ≃ Fin M) (x : Cube d) (hL : 3 ≤ L) :
    |feature d a b (x (d.pinLabel a))| ≤ (2:ℤ)^(((b:ℕ)+1)*L) := by
  rw [cubeFeature_eq d a b idx (fun _ => true)]
  exact J9FactorBounds.moment_abs_le _ _ _ hL (J9End.chart_tile_injective d a idx _)

#print axioms cube_card
#print axioms cubeFeature_eq
#print axioms cubeFeature_bound
end
end J8J9Grouped
