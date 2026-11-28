
import J6R24MeteredRecursionFrame
import J6R22ActiveCoeff
import J6R25StableCensusCompactRoot

/-! Root registers move across a proved precision identity only. The
prepared execution's measured outputs are then materialized once and
scanned with the original bit-width-aware U/V word scanner. -/
namespace J6R26StablePreparedRoot
open scoped Polynomial BigOperators
open Polynomial A1R10 AOracleMachineTime AOracleCoordinates J6R9Recursive
open J6R24MeteredRecursion J6R22Active J6R18ChildWrite
set_option maxHeartbeats 6500000
set_option maxRecDepth 1500

variable {f : ℤ[X]} {ell p q : ℕ}

def siteFrame (e : p=q) (F : Frame f q) : Frame f p :=
  cast (congrArg (Frame f) e.symm) F

def restoreFrame (e : p=q) (F : Frame f q)
    (got : Meter (Block (siteFrame e F) ell)) : Meter (Block F ell) := by
  subst q
  exact got

theorem restore_frame_receipt (e : p=q) (F : Frame f q)
    (got : Meter (Block (siteFrame e F) ell)) :
    F.decode (restoreFrame e F got).result=cast (congrArg (Box f ell) e) ((siteFrame e F).decode got.result) ∧
    (restoreFrame e F got).steps=got.steps := by
  subst q
  exact ⟨rfl,rfl⟩

section Gather
variable (F : Frame f p) (m : ℕ)
variable (sites : J6Recovery.Addr m→Meter (Block F ell))

def rowsOfSites : List (Meter (Block F ell)) := List.ofFn sites

def slotRead (i : J6Recovery.Addr m) : Meter (Block F ell) :=
  scanWord (jetGates F.hp F.sizePos ell) i.val ((rowsOfSites F m sites).map Meter.result)

def slotReadsFee : ℕ := ∑ i : J6Recovery.Addr m,(slotRead F m sites i).steps

theorem stored_slot_exact (i : J6Recovery.Addr m) :
    (slotRead F m sites i).result=(sites i).result ∧
    (slotRead F m sites i).steps≤(m+1)*(jetEntryWidth F.words.length ell p+2) := by
  let L := (rowsOfSites F m sites).map Meter.result
  have l : L.length=m+1 := by simp only [L,rowsOfSites,List.length_map,List.length_ofFn]
  obtain ⟨ex,cost⟩ := scanWord_exact (jetGates F.hp F.sizePos ell) L i.val
  have hi : i.val<L.length := l.symm ▸ i.isLt
  refine ⟨?_,?_⟩
  · change (scanWord (jetGates F.hp F.sizePos ell) i.val L).result=(sites i).result
    simp only [List.getD_eq_getElem?_getD,getElem?_pos L i.val hi,Option.getD_some] at ex
    simpa only [L,rowsOfSites,List.getElem_map,List.getElem_ofFn] using ex
  · simpa only [slotRead,←l] using cost

theorem stored_scan_bill :
    slotReadsFee F m sites ≤ (m+1)^2*(jetEntryWidth F.words.length ell p+2) := by
  unfold slotReadsFee
  calc
    _ ≤ ∑ _i : J6Recovery.Addr m,(m+1)*(jetEntryWidth F.words.length ell p+2) :=
      Finset.sum_le_sum (fun i _=>(stored_slot_exact F m sites i).2)
    _ = _ := by simp [pow_two,mul_assoc]

end Gather
#print axioms restore_frame_receipt
#print axioms stored_slot_exact
#print axioms stored_scan_bill
end J6R26StablePreparedRoot
