import J6R49DFSProbe
import J6R49DFSJetCongr
import J6R22ActiveSite

/-! A literal source centre with streamed subcalls. Encode its actual
binary masks, run the verified normalizer from its row roster, and
compute the same finite interpolation/quotient as the prior centre.
The legacy all-mode list is used only in the correctness theorem. -/
namespace J6R49DFS
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion

set_option autoImplicit false
set_option maxHeartbeats 4900000
set_option maxRecDepth 2300

variable {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ q k : ℕ}
variable {sel : Selector S Δ} {c : Call (PhysicalHost f ell)}
variable {d : Ready S Δ c} {t : Center S c}
local notation "M" => NativeMenu (shape S Δ sel) c t
local notation "pₜ" => registerPrecision S c t

noncomputable def directCentreJet (F : Frame f pₜ) (I : J6R16ModeCost.SiteTape sel d t q)
    (hq : 0<q) (hv : 0<ell) (hk : 0<k)
    (masks : Probe S c→Meter {m : List Bool // m.length=F.words.length})
    (roster : List (ℤ×ℕ))
    (child : Probe S c→M→Fin 64→Meter (Block F ell)) :
    Meter (JetTape F.words ell k) :=
  fullCenterM F.hp F.sizePos hv hk
    (fun z=>padCost (encodeProbe F.hp hv (masks z).result) (masks z).steps)
    (fun z=>runProbe F I hq hv (child z))
    (normalizerM F.hp F.sizePos hv hk (S.levelBits c.depth) t.val roster)

theorem same_center_jet_words (hf : f.Monic) (F : Frame f pₜ) (I : J6R16ModeCost.SiteTape sel d t q)
    (hq : 0<q) (hv : 0<ell) (hk : 0<k)
    (masks : Probe S c→Meter {m : List Bool // m.length=F.words.length})
    (roster : List (ℤ×ℕ)) (child : Probe S c→M→Fin 64→Meter (Block F ell))
    (prior : List M) (nd : prior.Nodup) (complete : ∀ β,β∈prior) :
    (directCentreJet F I hq hv hk masks roster child).result=
      (fullCenterM F.hp F.sizePos hv hk
        (fun z=>padCost (encodeProbe F.hp hv (masks z).result) (masks z).steps)
        (fun z=>groupedProbe F.hp F.sizePos hv prior (child z))
        (normalizerM F.hp F.sizePos hv hk (S.levelBits c.depth) t.val roster)).result := by
  unfold directCentreJet
  apply interchangeable_samples
  intro z
  exact streamed_probe_replaces_list hf F I hq hv (child z) prior nd complete

#print axioms directCentreJet
#print axioms same_center_jet_words
end J6R49DFS
