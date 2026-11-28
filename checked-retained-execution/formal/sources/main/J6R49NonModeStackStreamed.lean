import J6R49NonModeStackCenter
import J6R49DFSDirectCentre

/-! Bind the fixed-width pause observer to the actual R49 streamed
probe implementation. The record is used as a proof-side view of a
suspension, not as a modified center runner. -/
namespace J6R49NonModeStack
open scoped Polynomial
open AOracleMachineTime A1R10 A1R12 J6R22Active
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint
open J6R16ModeCost J6R24MeteredRecursion J6R49DFS
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4500000

variable {f : ℤ[X]} {ell : ℕ} {S : Params (f:=f) (ell:=ell)} {Δ q k : ℕ}
variable {sel : Selector S Δ} {c : Call (PhysicalHost f ell)}
variable {d : Ready S Δ c} {t : Center S c}
local notation "M" => NativeMenu (shape S Δ sel) c t
local notation "pₜ" => registerPrecision S c t
local notation "n" => J9PrintedSchedule.probeCount c.edges (2^S.levelBits c.depth)

noncomputable def observeStreamedCenter (F : Frame f pₜ) (I : SiteTape sel d t q)
    (hq : 0<q) (hv : 0<ell) (hk : 0<k)
    (masks : Probe S c→Meter {m : List Bool // m.length=F.words.length})
    (roster : List (ℤ×ℕ))
    (child : Probe S c→M→Fin 64→Meter (Block F ell)) (i : Probe S c) :
    List Bool × Meter (JetTape F.words ell k) :=
  let nodes := fun z=>padCost (encodeProbe F.hp hv (masks z).result) (masks z).steps
  let samples := fun z=>runProbe F I hq hv (child z)
  let normal := normalizerM F.hp F.sizePos hv hk (S.levelBits c.depth) t.val roster
  let saved := completedTerms F.hp F.sizePos hv hk nodes samples i
  let basis := basisM F.hp F.sizePos hv hk nodes i
  let later := paidJetSum F.hp F.sizePos (interpTerm F.hp F.sizePos hv hk nodes samples)
    ((probeOrder n).drop (i.val+1))
  ⟨pausedJetFields F.hp F.sizePos hv hk nodes samples i normal,
    resumeCenter F.hp F.sizePos hv hk saved basis (samples i) later normal n⟩

/-- The exact actual R49 center meter resumes from the completed probe
prefix, just one new probe reply, and the original suffix/quotient.
The bit count is only the numerical jet/basis/normalizer payload,
not the mode cursor, child result, scratch, or frame itself. -/
theorem streamed_center_has_literal_suspended_jets (hf : f.Monic)
    (F : Frame f pₜ) (I : SiteTape sel d t q)
    (hq : 0<q) (hv : 0<ell) (hk : 0<k)
    (masks : Probe S c→Meter {m : List Bool // m.length=F.words.length})
    (roster : List (ℤ×ℕ))
    (child : Probe S c→M→Fin 64→Meter (Block F ell)) (i : Probe S c) :
    let pause := observeStreamedCenter F I hq hv hk masks roster child i
    directCentreJet F I hq hv hk masks roster child=pause.2 ∧
      pause.1.length=(i.val+2)*(k*(ell*(f.natDegree*pₜ))) ∧
      pause.1.length≤(n+1)*(k*(ell*(f.natDegree*pₜ))) := by
  let nodes := fun z=>padCost (encodeProbe F.hp hv (masks z).result) (masks z).steps
  let samples := fun z=>runProbe F I hq hv (child z)
  let normal := normalizerM F.hp F.sizePos hv hk (S.levelBits c.depth) t.val roster
  exact ⟨full_center_pauses_at_literal_probe F.hp F.sizePos hv hk nodes samples normal i,
    native_frame_paused_jet_payload F hf hv hk nodes samples normal i⟩

#print axioms streamed_center_has_literal_suspended_jets
end J6R49NonModeStack
