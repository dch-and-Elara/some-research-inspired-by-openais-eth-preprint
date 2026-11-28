import A4R45PairSeats
import J6R10RepackPhysical

/-! Extend the chosen ordering in one ordered cell to a fully occupied
actual P11 packing. The destination addresses are real packet positions,
not a second chart with a different predecessor order. -/
namespace A4R45PhysicalFullChart
open P11FullPacking J6R10Repack
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1300000

variable {W A B G : Type*} [LinearOrder G] {a copies : ℕ}

noncomputable def physicalFibreChart (mask : MaskFamily a copies G) (c : Cell (Fin a) G) :
    {p : Physical a copies G // physicalCell mask p=c} ≃ Fin (copies * 2^a) where
  toFun z := (fullSlotChart mask z.val).2
  invFun slot := ⟨(fullSlotChart mask).symm (c,slot),by
    rw [←fullSlotChart_cell,Equiv.apply_symm_apply]⟩
  left_inv z := by
    apply Subtype.ext
    apply (fullSlotChart mask).injective
    rw [Equiv.apply_symm_apply]
    exact Prod.ext ((fullSlotChart_cell mask z.val).trans z.2).symm rfl
  right_inv slot := by simp

theorem actual_full_chart_prescribed {Hard : Type*} [Fintype Hard] [Fintype W] [Fintype G]
    (N : Network W A B) (rows : A→Fin a→G) (cols : B→Fin a→G)
    (mask : MaskFamily a copies G) (diag : Cell (Fin a) G)
    (room : ∀ c, Nat.card {w : W // declaredCell N rows cols w=c}=copies*2^a)
    (hard : Hard ↪ {w : W // declaredCell N rows cols w=diag})
    (planned : Hard ↪ {p : Physical a copies G // physicalCell mask p=diag}) :
    ∃ seat : W ≃ Physical a copies G,
      (∀ w, physicalCell mask (seat w)=declaredCell N rows cols w) ∧
      (∀ h, seat (hard h).val=(planned h).val) := by
  classical
  let U (c : Cell (Fin a) G) := {w : W // declaredCell N rows cols w=c}
  let V (c : Cell (Fin a) G) := {p : Physical a copies G // physicalCell mask p=c}
  letI (c : Cell (Fin a) G) : Fintype (U c) := Fintype.ofFinite _
  letI (c : Cell (Fin a) G) : Fintype (V c) := Fintype.ofFinite _
  have card (c : Cell (Fin a) G) : Fintype.card (U c)=Fintype.card (V c) := by
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,room c,
        Nat.card_congr (physicalFibreChart mask c),Nat.card_fin]
  obtain ⟨fixed,verified⟩ :=
    A4R45PairSeats.extend_finite_pair_embedding hard planned (card diag)
  let liftHard (c : Cell (Fin a) G) (hc : c=diag) (h : Hard) : U c :=
    ⟨(hard h).val,(hard h).property.trans hc.symm⟩
  have pieces (c : Cell (Fin a) G) : ∃ e : U c ≃ V c,
      ∀ hc : c=diag, ∀ h, (e (liftHard c hc h)).val=(planned h).val := by
    by_cases hc : c=diag
    · subst c
      refine ⟨fixed, ?_⟩
      intro proof h
      cases proof
      exact congrArg Subtype.val (verified h)
    · exact ⟨Fintype.equivOfCardEq (card c), fun e=>False.elim (hc e)⟩
  choose piece linked using pieces
  let raw :=
    (Equiv.sigmaFiberEquiv (declaredCell N rows cols)).symm.trans
      ((Equiv.sigmaCongrRight piece).trans
        (Equiv.sigmaFiberEquiv (physicalCell mask)))
  refine ⟨raw,?_,?_⟩
  · intro w
    change physicalCell mask (piece (declaredCell N rows cols w) ⟨w,rfl⟩).val=
      declaredCell N rows cols w
    exact (piece _ _).property
  · intro h
    have hc := (hard h).property
    change (piece (declaredCell N rows cols (hard h).val) ⟨(hard h).val,rfl⟩).val=
      (planned h).val
    have hh := linked (declaredCell N rows cols (hard h).val) hc h
    have hw : liftHard (declaredCell N rows cols (hard h).val) hc h =
      ⟨(hard h).val,rfl⟩ := Subtype.ext rfl
    rw [hw] at hh
    exact hh

def install_full_chart [Fintype G] (N : Network W A B)
    (rows : A→Fin a→G) (cols : B→Fin a→G) (mask : MaskFamily a copies G)
    (seat : W ≃ Physical a copies G)
    (typed : ∀ w, physicalCell mask (seat w)=declaredCell N rows cols w)
    (budget : Nat.card (Cell (Fin a) G)*(copies * 2^a)≤3*Nat.card W) :
    PhysicalPacking N a G where
  rowLabel:=rows
  colLabel:=cols
  copies:=copies
  mask:=mask
  seat:=seat.toEmbedding
  exactCell:=typed
  paddedBudget:=budget

#print axioms physicalFibreChart
#print axioms actual_full_chart_prescribed
#print axioms install_full_chart
end A4R45PhysicalFullChart
