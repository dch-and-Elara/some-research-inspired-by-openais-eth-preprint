import J6R24MeteredRecursionTreeLedger
import Mathlib.Data.Finset.Card

/-! The prepared arithmetic's literal child visit order. This enumerates
centre × binary probe × legal mode × 64 in the order of the actual
prepared finite lists. The canonical theorem-side slotOrder may be in
another order, and is used only to prove the occurrence-set receipt. -/
namespace J6R26DescriptorTree
open scoped Polynomial BigOperators
open Polynomial A1R10 AOracleMachineTime
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6R22Active J6R16ModeCost

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
variable {c : Call (PhysicalHost f ell)}
variable (d : Ready (printedParams (f:=f) (ell:=ell) s) (sourceDelta s) c)
variable {bank : Bank f} (D : ActiveDesc sel d bank)

def nativeSlots : List ((Plan sel).Slot c) :=
  D.centres.flatMap fun t=> (probeOrder _).flatMap fun z=> (D.tape t).modes.flatMap fun β=>
    (groupOrder 64).map fun g=>addressed d t z β g

theorem native_slots_complete (w : (Plan sel).Slot c) : w∈nativeSlots d D := by
  rcases w with ⟨⟨t,z,β,g⟩,ha⟩
  exact List.mem_flatMap.mpr ⟨t,D.centreComplete t,List.mem_flatMap.mpr
    ⟨z,probeOrder_mem z,List.mem_flatMap.mpr ⟨β,(D.tape t).modeComplete β,
      List.mem_map.mpr ⟨g,List.mem_ofFn.mpr ⟨g,rfl⟩,rfl⟩⟩⟩⟩

set_option maxHeartbeats 2600000 in
theorem native_slots_sum (hv : 0<ell) (price : (Plan sel).Slot c→ℕ) :
    ((nativeSlots d D).map price).sum=
     @Finset.sum ((Plan sel).Slot c) ℕ _ (@Finset.univ _ ((Plan sel).finiteSlot c)) price := by
  let go : ActiveChild (sel:=sel) (d:=d) bank := fun t z β g=>
    ⟨(zeroM (bank (registerPrecision S c t) (register_positive d t)).hp).result,
      price (addressed d t z β g)⟩
  have e := child_sum_exact d D hv go price (fun _ _ _ _=>rfl)
  simpa only [nativeSlots,list_sum_flat_map,List.map_map,Function.comp_apply,
    ActiveDesc.children,SiteTape.childBill,CentreDesc.site,probeEntryBill,bill,go]
    using e

theorem native_slots_order (hv : 0<ell) : (nativeSlots d D).Perm (slotOrder (Plan sel) c) := by
  classical
  letI : Fintype ((Plan sel).Slot c) := (Plan sel).finiteSlot c
  have hL : (nativeSlots d D).length=Fintype.card ((Plan sel).Slot c) := by
    simpa using native_slots_sum d D hv (fun _=>1)
  have hAll : (nativeSlots d D).toFinset=Finset.univ := by
    ext x
    simp only [List.mem_toFinset,Finset.mem_univ,iff_true]
    exact native_slots_complete d D x
  have hN : (nativeSlots d D).Nodup := by
    have H : (nativeSlots d D).toFinset.card=(nativeSlots d D).length := by
      rw [hAll,Finset.card_univ,hL]
    exact Multiset.toFinset_card_eq_card_iff_nodup.mp H
  unfold slotOrder
  exact List.perm_of_nodup_nodup_toFinset_eq hN (Finset.nodup_toList _)
    (by simpa using hAll)

variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable (T : Prepared cfg sel r hf)

noncomputable def ordered (c : Call (PhysicalHost f ell)) : List ((Plan sel).Slot c) := by
  classical
  exact if h : NativeReach (Plan sel) r c then
    if ha : (S).cutoff<c.edges then
      nativeSlots (ready_reachable cfg sel h T.rootStable ha) (T.active c h ha)
    else [] else []

theorem ordered_is_native (hc : NativeReach (Plan sel) r c) :
    (ordered T c).Perm (slotOrder (Plan sel) c) := by
  classical
  unfold ordered
  rw [dif_pos hc]
  split
  · exact native_slots_order _ _ T.vPositive
  · rename_i h
    have e : slotOrder (Plan sel) c=[] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro w _
      exact h w.property
    rw [e]

noncomputable def orderedChildren (c : Call (PhysicalHost f ell)) : List (Call (PhysicalHost f ell)) :=
  (ordered T c).map ((Plan sel).child c)

theorem ordered_children_same (hc : NativeReach (Plan sel) r c) :
    (orderedChildren T c).Perm (childList (Plan sel) c) :=
  (ordered_is_native T hc).map ((Plan sel).child c)

#print axioms native_slots_complete
#print axioms native_slots_sum
#print axioms native_slots_order
#print axioms ordered_children_same
end J6R26DescriptorTree
