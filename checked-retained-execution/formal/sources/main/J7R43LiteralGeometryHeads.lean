import J9R20SameFileGeometry
import J9R20SameFileLiteralTables

/-! The audited source geometry supplies the exact head label for each
printed row, pin and old column: take any of that owner's real ports in
the preserved declaration. No independent vertex-word callback. -/
namespace J7R43Literal
open scoped Classical
open P11FullPacking J6R10Repack J6R9PacketScopes J6R14SpecializedBox
open J7SourceLabels J7PrintedParamsGraph J7ToJ8Incidence J8Physical J9R20SameFile
noncomputable section
set_option autoImplicit false

variable {Pair H : Type} [Fintype Pair] [Fintype H]
variable (ends : H×Bool≃Pin Pair×Fin 3) {a b : ℕ}
variable (G : SourceGeometry ends a b) (i : Fin a) (hi : i.val=0)

include hi in
theorem original_geometry_row_words (r : Subdivision Pair (OrdinaryRow Pair H)) :
    G.wordsR r i = G.layout.rowLabel r := by
  let w : J8Physical.Wire (Subdivision Pair (OrdinaryRow Pair H)) := (r,false)
  have h := congrArg (fun c : Cell (Fin a) (Fin 64) => (c i).1) (G.declared w)
  change rowGroup _ i (G.layout.seat w) = G.wordsR r i at h
  exact h.symm.trans (G.rowHead i hi w)

include hi in
theorem original_geometry_pin_words (s : Pin Pair) :
    G.wordsC (.inl s) i = G.layout.pinLabel s := by
  let w := pinWire G.layout s
  have h := congrArg (fun c : Cell (Fin a) (Fin 64) => (c i).2) (G.declared w)
  change colGroup _ i (G.layout.seat w) = G.wordsC (colOwner G.layout w) i at h
  have hw : colOwner G.layout w = .inl s := by simp [w,colOwner]
  rw [hw] at h
  exact h.symm.trans ((G.colHead i hi w).trans (pinWire_colLabel G.layout s))

include hi in
theorem original_geometry_old_words (v : PrintedOld Pair H) :
    G.wordsC (.inr v) i = G.layout.colLabel v := by
  have hn : 0<Nat.card (Ports (column ends cycle) v) := by
    rw [printed_old_arity ends]
    rcases v with _|(_|_) <;> first | exact (by decide : 0<(3:ℕ)) | exact (by decide : 0<(2:ℕ))
  let u := Classical.choice (Nat.card_pos_iff.mp hn).1
  let w := G.layout.column.symm (.inr ⟨v,u⟩)
  have h := congrArg (fun c : Cell (Fin a) (Fin 64) => (c i).2) (G.declared w)
  change colGroup _ i (G.layout.seat w) = G.wordsC (colOwner G.layout w) i at h
  have hw : colOwner G.layout w = .inr v := by simp [w,colOwner]
  have hw' : actualColLabel G.layout w = G.layout.colLabel v := by simp [w,actualColLabel]
  rw [hw] at h
  exact h.symm.trans ((G.colHead i hi w).trans hw')

#print axioms original_geometry_row_words
#print axioms original_geometry_pin_words
#print axioms original_geometry_old_words
end
end J7R43Literal
