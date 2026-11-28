import J6R33PageIndexedBirthAtlas

set_option autoImplicit false
set_option warningAsError true

/-! Page identity survives the two actual covariate tables: the
resident mask writer and the packer's seat key use the same page,
though their byte formats are intentionally different. -/
namespace J6R33PageIndexedBirth
open AOracleMachineTime J6R15ModeCost J6R17ModeTape
open P11FullPacking J6R14LayoutCost J6R30GeneratedRootLayout J6R31RootResidentTables
open J6R32ChildResidentTransfer J6R27OriginalGate J6R21Ancestor J6R30ProducedGateRegistry
open J6Mesh J6R23PaddingCensus

theorem generated_and_mask_page_order {q b : ℕ} (a w : ℕ)
    (hq : 0<q) (copies : Word q) (count : copies.val=b) (addrFit : b≤2^w) :
    (writeRequests a w hq copies).result.map Request.owner =
      (writeChildMaskBank hq a copies).result.map MaskRow.address := by
  rw [(write_requests_exact a w hq copies count addrFit).1,
    (child_mask_bank_exact hq a copies count).1,List.map_map,List.map_map]
  rfl

theorem source_key_is_root_seat_key {m q : ℕ} (k : Page (a m) (K m) (Fin 64)) :
    (sourceRequest q (RootKey m) k).key=residentPageKey m k := rfl

/-- A nonpage does not silently acquire a value. The actual route
scans the whole bank and pays every header comparison, including the
end-of-bank test. -/
theorem exact_fee_for_foreign_page {D : Type*} {a b w : ℕ}
    (addr : Word (w+13*a)) (datum : Page a b (Fin 64)→D)
    (foreignPage : ¬ ∃ k : Page a b (Fin 64),childPageKey w k=addr) :
    let bank : List (RefRow (w+13*a) D) :=
      (orderedChildPages a b).map (fun k=>⟨childPageKey w k,datum k⟩)
    locate addr bank=⟨none,locateFee (w+13*a) (pagesCount a b)⟩ := by
  let bank : List (RefRow (w+13*a) D) :=
    (orderedChildPages a b).map (fun k=>⟨childPageKey w k,datum k⟩)
  have noKey (row : RefRow (w+13*a) D) (h : row∈bank) : row.address≠addr := by
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp h
    exact fun eq=>foreignPage ⟨k,eq⟩
  have L : bank.length=pagesCount a b := by
    unfold bank pagesCount
    rw [List.length_map,(child_pages_complete a b).2.2]
  have miss := ref_miss_exact addr bank noKey
  change locate addr bank=_
  rw [←L]
  exact miss

#print axioms generated_and_mask_page_order
#print axioms source_key_is_root_seat_key
#print axioms exact_fee_for_foreign_page
end J6R33PageIndexedBirth
