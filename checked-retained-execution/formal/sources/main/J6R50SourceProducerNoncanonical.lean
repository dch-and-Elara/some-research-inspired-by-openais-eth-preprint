import J6R50SourceProducerReplay

/-! Incidence and the labels alone do not select the physical chart.
An arbitrary legal change of mask can be accompanied by the
canonical in-page seat transformation without changing any ordered
cell or capacity. Therefore an unspecified fixed selector cannot be
reconstructed by incidence-only computation of raw resident bytes. -/
namespace J6R50SourceProducer
open scoped Classical
open P11FullPacking J6R10Repack J6R32ChildResidentTransfer J6R27OriginalGate J6R24LegalLayout
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1800
set_option maxHeartbeats 4200000
set_option Elab.async false
noncomputable section

def withSelectedMask {E R C : Type} {a : ℕ} {N : Network E R C}
    (P : PhysicalPacking N a (Fin 64)) (mask : MaskFamily a P.copies (Fin 64)) :
    PhysicalPacking N a (Fin 64) where
  rowLabel := P.rowLabel
  colLabel := P.colLabel
  copies := P.copies
  mask := mask
  seat := (P.seat.trans (twistChart P.mask).toEmbedding).trans (twistChart mask).toEmbedding
  exactCell e := by
    change physicalCell mask (twistSeat mask (twistSeat P.mask (P.seat e)))=_
    rw [twist_preserves_ordered_cell]
    have h := twist_preserves_ordered_cell P.mask (twistSeat P.mask (P.seat e))
    rw [twist_seat_involutive] at h
    rw [←h]
    exact P.exactCell e
  paddedBudget := P.paddedBudget

theorem reselected_mask_same_geometry_budget {E R C : Type} {a : ℕ} {N : Network E R C}
    (P : PhysicalPacking N a (Fin 64)) (mask : MaskFamily a P.copies (Fin 64)) :
    (withSelectedMask P mask).rowLabel=P.rowLabel ∧
      (withSelectedMask P mask).colLabel=P.colLabel ∧ (withSelectedMask P mask).copies=P.copies :=
  ⟨rfl,rfl,rfl⟩

theorem different_hot_bit_gives_different_tape {a copies q : ℕ}
    {m0 m1 : MaskFamily a copies (Fin 64)} (page : Page a copies (Fin 64)) (i : Fin a)
    (different : selectedMaskBit m0 page i≠selectedMaskBit m1 page i) :
    (orderedChildPages a copies).map (encodeMaskRow (q:=q) m0) ≠
      (orderedChildPages a copies).map (encodeMaskRow (q:=q) m1) := by
  intro h
  have point := List.map_inj_left.mp h page ((child_pages_complete a copies).2.1 page)
  have bits := congrArg (fun x : MaskRow q=>x.bits) point
  change List.ofFn (selectedMaskBit m0 page)=List.ofFn (selectedMaskBit m1 page) at bits
  exact different (congrFun (List.ofFn_inj.mp bits) i)

theorem no_common_raw_mask_tape_for_unspecified_selector
    {E R C : Type} {a q : ℕ} {N : Network E R C}
    (P : PhysicalPacking N a (Fin 64)) (page : Page a P.copies (Fin 64)) (i : Fin a)
    (hot : (page.1.val i).1≠(page.1.val i).2) :
    let P0 := withSelectedMask P (fun _ _ _=>false)
    let P1 := withSelectedMask P (fun _ _ _=>true)
    P0.rowLabel=P1.rowLabel ∧ P0.colLabel=P1.colLabel ∧ P0.copies=P1.copies ∧
      ¬∃ bytes : List (MaskRow q),
        bytes=(orderedChildPages a P0.copies).map (encodeMaskRow P0.mask) ∧
        bytes=(orderedChildPages a P1.copies).map (encodeMaskRow P1.mask) := by
  refine ⟨rfl,rfl,rfl,?_⟩
  rintro ⟨bytes,l,r⟩
  apply different_hot_bit_gives_different_tape (m0:=fun _ _ _=>false) (m1:=fun _ _ _=>true) page i
  · unfold selectedMaskBit
    simp only [dif_pos hot]
    decide
  · exact l.symm.trans r

#print axioms reselected_mask_same_geometry_budget
#print axioms different_hot_bit_gives_different_tape
#print axioms no_common_raw_mask_tape_for_unspecified_selector
end
end J6R50SourceProducer