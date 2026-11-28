import J6R33GeneratedChildSitePage
import J6R33GeneratedChildSiteAtlas

/-! The actual R33 atlas page has one row / column at most per physical
seat, and its complete mode tape obeys the real padded budget. These
bounds concern the checked page, not a separately supplied list. -/
namespace J6R58LeafScale
open scoped Polynomial Classical
open AOracleMachineTime A1R10 J6R17ModeTape J6R27OriginalGate
open J6R30ProducedGateRegistry J6R32ChildResidentTransfer J6R33PageIndexedBirth
open J6R33GeneratedChildSite J6R10Repack P11FullPacking J6R9PacketChild
open J6R18ChildWrite J6R9Recursive J6R20Ancestor
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 20000000
set_option maxRecDepth 3300

private theorem nodup_length_le_fin {A : Type*} {n : ℕ} (xs : List A)
    (tag : A→Fin n) (inj : Function.Injective tag) (unique : xs.Nodup) :
    xs.length≤n := by
  have h := (unique.map inj).length_le_card
  simpa only [List.length_map,Fintype.card_fin] using h

noncomputable section
variable {E A B : Type} {N : Network E A B}
variable {a q p ell code : ℕ}
variable {P : PhysicalPacking N a (Fin 64)} {i : Fin a} {R : ChildResidents a q}
variable (H : ResidentReceipt P i p R)
variable {fw : List (A1R10.Word p)} {f : ℤ[X]}
variable [DecidableEq (Page a P.copies (Fin 64))]

theorem true_padded_atlas_area :
    Nat.card (Page a P.copies (Fin 64))*2^a≤3*Nat.card E := by
  rw [total_slots P.mask]
  exact P.paddedBudget

theorem actual_mode_roster_fits_padded_area :
    H.modes.length≤3*Nat.card E*p := by
  have h := (Nat.card_fin H.modes.length).symm.trans (Nat.card_congr (RosterIndex H))
  have hc : Nat.card (J6R15ModeCost.Crossing (G:=Fin 64) (pages:=P.copies) i)≤
      Nat.card (Page a P.copies (Fin 64)) :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have ht : (2:ℕ)^(i.val+1)≤2^a :=
    Nat.pow_le_pow_right (by decide) i.isLt
  show H.modes.length≤_
  calc
    _=Nat.card (J6R15ModeCost.Crossing (G:=Fin 64) (pages:=P.copies) i)*
        (2^(i.val+1)*(p-1)) := by
      simpa only [PacketMode,J6R15ModeCost.Mode,Nat.card_prod,Nat.card_fin] using h
    _≤Nat.card (Page a P.copies (Fin 64))*(2^a*p) :=
      Nat.mul_le_mul hc (Nat.mul_le_mul ht (Nat.sub_le _ _))
    _=(Nat.card (Page a P.copies (Fin 64))*2^a)*p := (Nat.mul_assoc _ _ _).symm
    _≤_ := Nat.mul_le_mul_right _ (true_padded_atlas_area (P:=P))

theorem actual_rows_in_one_page_le_mesh (g : Fin 64) (k : Page a P.copies (Fin 64)) :
    (sourceRows P i g k H.edges).length≤2^a := by
  let tag (u : RowsOf P i g k) := (P.seat u.val).2
  have inj : Function.Injective tag := by
    intro u v same
    apply Subtype.ext
    apply P.seat.injective
    have hu : (P.seat u.val).1=k := congrArg Prod.snd u.property
    have hv : (P.seat v.val).1=k := congrArg Prod.snd v.property
    exact Prod.ext (hu.trans hv.symm) same
  exact nodup_length_le_fin _ tag inj (scan_subtype_nodup _ _ H.edgesUnique)

theorem actual_columns_in_one_page_le_mesh (g : Fin 64) (k : Page a P.copies (Fin 64)) :
    (sourceCols P i g k H.edges).length≤2^a := by
  let tag (u : ColsOf P i g k) := (P.seat u.val).2
  have inj : Function.Injective tag := by
    intro u v same
    apply Subtype.ext
    apply P.seat.injective
    exact Prod.ext (u.property.2.trans v.property.2.symm) same
  exact nodup_length_le_fin _ tag inj (scan_subtype_nodup _ _ H.edgesUnique)

theorem actual_published_page_dimensions
    {C : Common fw a (q+1) code ((q-a)+13*a)} {hp : 0<p} {hv : 0<ell}
    {fit : i.val+1≤q+1}
    {hMod : Modulus p hp fw=NativeProbeRing.liftPoly p f}
    {node : Box f ell p} {g : Fin 64} {β : Legal P i p} {k : Page a P.copies (Fin 64)}
    (page : PageReceipt H C hp hv fit hMod node g β k) :
    page.fields.rows.length≤2^a ∧ page.fields.cols.length≤2^a ∧
      page.fields.modes.length≤3*Nat.card E*p := by
  constructor
  · rw [page.rowSlots,List.length_map]
    exact actual_rows_in_one_page_le_mesh H g k
  · constructor
    · rw [page.colSlots,List.length_map]
      exact actual_columns_in_one_page_le_mesh H g k
    · rw [page.modeList,List.length_ofFn]
      exact actual_mode_roster_fits_padded_area H

#print axioms true_padded_atlas_area
#print axioms actual_mode_roster_fits_padded_area
#print axioms actual_rows_in_one_page_le_mesh
#print axioms actual_columns_in_one_page_le_mesh
#print axioms actual_published_page_dimensions
end
end J6R58LeafScale
