import J6R49DFSDirectCentre
import J6R48BitCostLoaderDelta

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 13000000
set_option maxRecDepth 2500

/-! Genuine boundary of the streamed centre: given mask *word validity*
alone, arbitrary extra charging preserves the complete value. Thus no
uniform actual-frame bound follows merely from a decoded receipt. -/
namespace J6R49Cost
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R24MeteredRecursion J6R48BitCost J6R49DFS

variable {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ q k : ℕ}
variable {sel : Selector S Δ} {c : Call (PhysicalHost f ell)}
variable {d : Ready S Δ c} {t : Center S c}
local notation "M" => NativeMenu (shape S Δ sel) c t
local notation "pₜ" => registerPrecision S c t

theorem actual_streamed_loader_boundary (F : Frame f pₜ) (I : J6R16ModeCost.SiteTape sel d t q)
    (hq : 0<q) (hv : 0<ell) (hk : 0<k)
    (mask : Probe S c→Meter {m : List Bool // m.length=F.words.length})
    (rows : List (ℤ×ℕ)) (child : Probe S c→M→Fin 64→Meter (Block F ell)) (extra : ℕ) :
    let n := J9PrintedSchedule.probeCount c.edges (2^(S.levelBits c.depth))
    let added := fun i=>padCost (mask i) extra
    (∀ i,(added i).result=(mask i).result) ∧
    Delta (directCentreJet F I hq hv hk added rows child)
      (directCentreJet F I hq hv hk mask rows child) (n*(n*extra)) := by
  let n := J9PrintedSchedule.probeCount c.edges (2^(S.levelBits c.depth))
  let N := normalizerM F.hp F.sizePos hv hk (S.levelBits c.depth) t.val rows
  let sample := fun z : Probe S c => runProbe F I hq hv (child z)
  let x := fun z : Probe S c =>
    padCost (encodeProbe F.hp hv (mask z).result) ((padCost (mask z) extra).steps)
  let y := fun z : Probe S c =>
    padCost (encodeProbe F.hp hv (mask z).result) (mask z).steps
  have eq (i : Probe S c) : Delta (x i) (y i) extra := by
    refine ⟨rfl,?_⟩
    simp only [x,y,padCost]
    omega
  let xd := interpPrefix F.hp F.sizePos hv hk x sample
  let yd := interpPrefix F.hp F.sizePos hv hk y sample
  let Q := divideJet F.hp F.sizePos hv hk N.result
  have load : Delta xd yd (n*(n*extra)) :=
    interpolation_load_delta F.hp F.sizePos hv hk x y sample extra eq
  refine ⟨fun _=>rfl,⟨?_,?_⟩⟩
  · change (Q xd.result).result=(Q yd.result).result
    rw [load.value]
  · change N.steps+xd.steps+(Q xd.result).steps+4 =
      N.steps+yd.steps+(Q yd.result).steps+4+n*(n*extra)
    rw [load.value,load.fee]
    omega

#print axioms actual_streamed_loader_boundary
end J6R49Cost

