import J6R49CostCentreKernel
import J6R49CostProbeCensus
import J6R49DFSDirectCentre

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 14500000
set_option maxRecDepth 2500

/-! Arithmetic receipt for the actual streamed centre, not a bound for
a value-equal interpreter. Coefficient-frame and node-loader tariffs
remain explicit. Child calls are charged through the indexed address bill. -/
namespace J6R49Cost
open scoped Polynomial BigOperators
open AOracleMachineTime A1R10 A1R11 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R25PreparedSupply J6R32StatefulArithmetic
open J6R48DFS J6R49DFS

variable {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ q k : ℕ}
variable {sel : Selector S Δ} {c : Call (PhysicalHost f ell)}
variable {d : Ready S Δ c} {t : Center S c}
local notation "M" => NativeMenu (shape S Δ sel) c t
local notation "pₜ" => registerPrecision S c t

noncomputable def streamedProbeTariff (F : Frame f pₜ) (I : J6R16ModeCost.SiteTape sel d t q) : ℕ :=
  (16*q+14+4*(I.words.length+1)*(q+1))+
  uvWidth F.words.length ell pₜ+
  Nat.card M*perModeArithmetic F.words.length ell pₜ F.hp+
  (Nat.card M+1)*J6R15ModeCost.delayCap q I.words.length

noncomputable def centreChildBill (F : Frame f pₜ)
    (child : Probe S c  →  M  →  Fin 64  →  Meter (Block F ell)) : ℕ :=
  ((probeOrder (J9PrintedSchedule.probeCount c.edges (2^(S.levelBits c.depth)))).map
    (fun z => actualProbeChildBill F (child z))).sum

theorem direct_streamed_centre_arithmetic_bill (F : Frame f pₜ)
    (I : J6R16ModeCost.SiteTape sel d t q) (hq : 0<q) (hv : 0<ell) (hk : 0<k)
    (masks : Probe S c → Meter {m : List Bool // m.length=F.words.length})
    (rows : List (ℤ×ℕ)) (child : Probe S c → M → Fin 64 → Meter (Block F ell))
    (nd : (rows.map Prod.fst).Nodup)
    (rowsExact : (rows.map Prod.fst).toFinset=(active (S.levelBits c.depth) c.edges (S.levelWidth c.depth)).erase t.val)
    (ord : ∀ x∈rows,x.2=order c.edges (S.levelWidth c.depth) x.1) :
    let n := J9PrintedSchedule.probeCount c.edges (2^(S.levelBits c.depth))
    let node := fun z : Probe S c=>padCost (encodeProbe F.hp hv (masks z).result) (masks z).steps
    (directCentreJet F I hq hv hk masks rows child).steps ≤ centreChildBill F child+
      (n*streamedProbeTariff F I+
        normalizerFee F.words.length ell pₜ (S.levelBits c.depth) k F.hp rows+
        ((probeOrder n).map (needsAt node)).sum+
        interpExtra F.words.length ell pₜ k n F.hp+quotientFee F.words.length ell pₜ k F.hp+4) := by
  let n := J9PrintedSchedule.probeCount c.edges (2^(S.levelBits c.depth))
  let node := fun z : Probe S c=>padCost (encodeProbe F.hp hv (masks z).result) (masks z).steps
  let sample := fun z : Probe S c => runProbe F I hq hv (child z)
  have core := full_rostered_center_actual_bill F.hp F.sizePos hv hk node sample
    (S.levelBits c.depth) c.edges (S.levelWidth c.depth) t.property rows nd rowsExact ord
  let children := fun z : Probe S c => (⟨(), actualProbeChildBill F (child z)⟩ : Meter Unit)
  have H := bill_mono sample children (probeOrder n) (streamedProbeTariff F I)
    (fun z _ => actual_streamed_probe_indexed_bill F I hq hv (child z))
  change bill sample (probeOrder n) ≤ bill children (probeOrder n)+(probeOrder n).length*streamedProbeTariff F I at H
  have len : (probeOrder n).length=n := List.length_ofFn
  rw [len] at H
  change _ ≤ centreChildBill F child+n*streamedProbeTariff F I at H
  change (directCentreJet F I hq hv hk masks rows child).steps ≤ bill sample (probeOrder n)+
    (normalizerFee F.words.length ell pₜ (S.levelBits c.depth) k F.hp rows+
      ((probeOrder n).map (needsAt node)).sum+interpExtra F.words.length ell pₜ k n F.hp+
      quotientFee F.words.length ell pₜ k F.hp+4) at core
  change (directCentreJet F I hq hv hk masks rows child).steps ≤ centreChildBill F child+
      (n*streamedProbeTariff F I+normalizerFee F.words.length ell pₜ (S.levelBits c.depth) k F.hp rows+
        ((probeOrder n).map (needsAt node)).sum+interpExtra F.words.length ell pₜ k n F.hp+
        quotientFee F.words.length ell pₜ k F.hp+4)
  exact core.trans (by omega)

#print axioms streamedProbeTariff
#print axioms centreChildBill
#print axioms direct_streamed_centre_arithmetic_bill
end J6R49Cost

