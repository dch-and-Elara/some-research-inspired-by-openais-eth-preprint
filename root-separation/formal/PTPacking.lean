import PTAdmissibility
import RootPacking

namespace RootSeparation.Preprocessing

open S11 SourceDensity Finset

variable {W X Y P : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype P]
set_option linter.unusedSectionVars false
variable
  [DecidableEq X] [DecidableEq Y]

theorem array_cell_count (s d : ℕ) :
    Fintype.card (RootCell (labelLength s d)) = arrayCells s d := by
  rw [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_fin,← pow_add]
  unfold arrayCells
  congr 1
  omega

/-- The actual prefix collision search and source padded cell packing
apply at every active depth once the two degree bounds have been preserved. -/
theorem active_packing {s d : ℕ} (row : W → X) (col : W → Y)
    (checks : ActiveNumbers s d (Fintype.card W))
    (hr : ∀ v, fiberCount row v ≤ degreeEnvelope s)
    (hc : ∀ v, fiberCount col v ≤ degreeEnvelope s) :
    let a := labelLength s d
    let L := packetLength s d
    let cell := cellAt row col (selectedLabels row col (fun _ : Fin a => (0 : Fin 64)))
    ∃ G : Packing W (S8.Packet (Fin a) (Fin 64) (exactPad cell)) a L,
      G.cell = cell ∧ CollisionCertificate G.cell (degreeEnvelope s : ℚ) ∧
        Fintype.card (S8.Packet (Fin a) (Fin 64) (exactPad cell)) * L ≤ 3*Fintype.card W := by
  classical
  intro a L cell
  have hcap := checks.collisionPacking
  rw [← array_cell_count] at hcap
  have hslots := checks.enoughSlots
  rw [← array_cell_count] at hslots
  have cert : CollisionCertificate cell (degreeEnvelope s : ℚ) := by
    constructor
    · exact selected_collision row col _ _ hr hc
    · exact_mod_cast hcap
  obtain ⟨G,hG,hpack⟩ := exact_packets cell (degreeEnvelope s : ℚ) cert hslots
  exact ⟨G,hG,by rwa [hG],hpack⟩

abbrev GroupWires {a : ℕ} (cell : W → RootCell a) (j : Fin a) (g : Fin 64) :=
  {w : W // (cell w).1 j = g} ⊕ {w : W // (cell w).2 j = g}

/-- One wire in the child per retained input port. A wire that has both
ports in the group contributes twice, once to each side of the sum. -/
theorem group_wire_shrink {a : ℕ} (cell : W → RootCell a) {Δ : ℚ}
    (cert : CollisionCertificate cell Δ) (j : Fin a) (g : Fin 64) :
    64*Fintype.card (GroupWires cell j g) ≤ 6*Fintype.card W := by
  have h₁ := packet_group_quota cell Δ cert j false g
  have h₂ := packet_group_quota cell Δ cert j true g
  simp only [Bool.false_eq_true, if_false, if_true] at h₁ h₂
  have h₁' : (Fintype.card {w : W // (cell w).1 j = g} : ℚ) ≤ 3 * Fintype.card W / 64 := by
    simpa only [Fintype.card_subtype,fiberCount] using h₁
  have h₂' : (Fintype.card {w : W // (cell w).2 j = g} : ℚ) ≤ 3 * Fintype.card W / 64 := by
    simpa only [Fintype.card_subtype,fiberCount] using h₂
  rw [Fintype.card_sum]
  exact_mod_cast (show (64:ℚ)*((Fintype.card {w : W // (cell w).1 j = g} : ℚ) +
    (Fintype.card {w : W // (cell w).2 j = g} : ℚ)) ≤ 6*Fintype.card W by linarith)

def childPacket {a L : ℕ} (G : Packing W P a L) (j : Fin a) (g : Fin 64) :
    GroupWires G.cell j g → P
  | .inl w => (G.position w.val).1
  | .inr w => (G.position w.val).1

def childOld {a : ℕ} (cell : W → RootCell a) (j : Fin a) (g : Fin 64)
    (row : W → X) (col : W → Y) : GroupWires cell j g → X ⊕ Y
  | .inl w => .inl (row w.val)
  | .inr w => .inr (col w.val)

theorem child_packet_degree {a L : ℕ} [DecidableEq P]
    (G : Packing W P a L) (j : Fin a) (g : Fin 64) (p : P) :
    fiberCount (childPacket G j g) p ≤ 2*L := by
  have ht : (univ : Finset (Bool × Fin L)).card = 2*L := by simp
  rw [fiberCount, ← ht]
  let tag : GroupWires G.cell j g → Bool × Fin L := fun w => match w with
    | .inl u => (false,(G.position u.val).2)
    | .inr u => (true,(G.position u.val).2)
  apply card_le_card_of_injOn tag
  · intro w hw
    exact mem_univ _
  · intro v hv w hw he
    have hleft : childPacket G j g v = p := (mem_filter.mp hv).2
    have hright : childPacket G j g w = p := (mem_filter.mp hw).2
    rcases v with (v | v) <;> rcases w with (w | w)
    all_goals
      simp only [childPacket] at hleft hright
      simp only [tag, Prod.mk.injEq, Bool.false_eq_true, Bool.true_eq_false, false_and,
        true_and] at he
    all_goals
      apply congrArg _
      exact Subtype.ext (G.position.injective (Prod.ext (hleft.trans hright.symm) he))

theorem child_old_degree {a : ℕ} (cell : W → RootCell a) (j : Fin a) (g : Fin 64)
    (row : W → X) (col : W → Y) (Δ : ℕ) (hr : ∀ v, fiberCount row v ≤ Δ)
    (hc : ∀ v, fiberCount col v ≤ Δ) (p : X ⊕ Y) :
    fiberCount (childOld cell j g row col) p ≤ Δ := by
  cases p with
  | inl x =>
    apply le_trans _ (hr x)
    unfold fiberCount
    let base : GroupWires cell j g → W := Sum.elim Subtype.val Subtype.val
    apply card_le_card_of_injOn base
    · rintro (v | v) hv <;> simp [childOld,base] at hv ⊢
      exact hv
    · rintro (v | v) hv (w | w) hw he <;> simp [childOld,base] at hv hw he
      exact congrArg Sum.inl (Subtype.ext he)
  | inr y =>
    apply le_trans _ (hc y)
    unfold fiberCount
    let base : GroupWires cell j g → W := Sum.elim Subtype.val Subtype.val
    apply card_le_card_of_injOn base
    · rintro (v | v) hv <;> simp [childOld,base] at hv ⊢
      exact hv
    · rintro (v | v) hv (w | w) hw he <;> simp [childOld,base] at hv hw he
      exact congrArg Sum.inr (Subtype.ext he)

#print axioms active_packing
#print axioms group_wire_shrink
#print axioms child_packet_degree
#print axioms child_old_degree

end RootSeparation.Preprocessing
