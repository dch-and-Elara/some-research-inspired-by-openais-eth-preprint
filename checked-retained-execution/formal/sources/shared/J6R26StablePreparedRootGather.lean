
import J6R26StablePreparedRootFrame
import J6R25StableCensusCompactRoot

/-! Metered outer execution on the stable root. No supplied raw slots:
they are produced from the requested Prepared subtrees by the actual
zero-mode probes, grouped products and unit interpolation, then the
same-layout R25 census and count program consume the materialized bank. -/
namespace J6R26StablePreparedRoot
open scoped Classical Polynomial BigOperators
open Polynomial J6R24LegalLayout J6Mesh J6R9Recursive J6OrientedHost
open Std.Sat J7R10Plant J6R22RootReadout J6R25StableCensus J6R18ChildWrite
open A1R10 AOracleMachineTime AOracleCoordinates J6R24MeteredRecursion J6R22Active
set_option linter.unusedSectionVars false
set_option maxHeartbeats 16000000
set_option maxRecDepth 2200

def gatherCost {f : ℤ[X]} {p ell : ℕ} (F : Frame f p) (m : ℕ)
    (sites : J6Recovery.Addr m→Meter (Block F ell)) : ℕ :=
  ((rowsOfSites F m sites).map Meter.steps).sum+
    (m+1)^2*(jetEntryWidth F.words.length ell p+2)+
    (m+1)*(jetEntryWidth F.words.length ell p+4)+6

def countFromMeasuredSlots {f : ℤ[X]} {p ell B R : ℕ} (F : Frame f p) (hb : 0<B) (hr : 0<R)
    (m l q width : ℕ) (cells : J6R14LayoutCost.CellWord)
    (sites : J6Recovery.Addr m→Meter (Block F ell)) : Meter (Word R) :=
  let bank := rowsOfSites F m sites
  let stored := bank.map Meter.result
  let scan := fun (i : J6Recovery.Addr m) => scanWord (jetGates F.hp F.sizePos ell) i.val stored
  let slots := fun (i : J6Recovery.Addr m) => (scan i).result
  let readout := compactStableCount F.hp hb hr m l q width slots cells
  ⟨readout.result,readout.steps+(bank.map Meter.steps).sum+(∑ i : J6Recovery.Addr m,(scan i).steps)+
    stored.length*(jetEntryWidth F.words.length ell p+4)+6⟩

theorem metered_slot_append {f : ℤ[X]} {p ell B R : ℕ} (F : Frame f p) (hb : 0<B) (hr : 0<R)
    (m l q width : ℕ) (cells : J6R14LayoutCost.CellWord)
    (sites : J6Recovery.Addr m→Meter (Block F ell)) :
    let A := countFromMeasuredSlots F hb hr m l q width cells sites
    let R' := compactStableCount F.hp hb hr m l q width
      (fun i=>(slotRead F m sites i).result) cells
    A.result=R'.result ∧ A.steps≤R'.steps+gatherCost F m sites := by
  have hFee := stored_scan_bill F m sites
  refine ⟨rfl,?_⟩
  change
    (compactStableCount F.hp hb hr m l q width (fun i=>(slotRead F m sites i).result) cells).steps+
      ((rowsOfSites F m sites).map Meter.steps).sum+slotReadsFee F m sites+
      ((rowsOfSites F m sites).map Meter.result).length*(jetEntryWidth F.words.length ell p+4)+6≤_
  rw [List.length_map,show (rowsOfSites F m sites).length=m+1 from List.length_ofFn]
  unfold gatherCost
  omega

#print axioms metered_slot_append
end J6R26StablePreparedRoot
