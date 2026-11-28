import V8R45PooledLiteralRootHook
import V8R45PooledLiteralDispatch

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3800000
set_option maxRecDepth 2800

/-! For the optional canonical roster, reindex the actual root Probe,
showing byte-for-byte equality of the binary words under the two names. -/
namespace V8R45PooledLiteral
open scoped Classical Polynomial
open Polynomial V8PooledRange V8PooledMenu.FiveCopy
open J6R12Blueprint J6R9Recursive J6R10Repack J6ActiveRun J1PPrinted
noncomputable section

private theorem chosenRep_finCongr (e : ℕ) {j j' : ℕ}
    (h : j=j') (fit : j≤2^e) (fit' : j'≤2^e) (i : Fin j) :
    NativeProbeRing.chosenRep e j' fit' (finCongr h i) =
      NativeProbeRing.chosenRep e j fit i := by
  subst j'
  rfl

private theorem readProbe_transport (f : ℤ[X]) {p q : ℕ}
    (h : p=q) (w : Fin f.natDegree → Bool) :
    cast (congrArg (Residue f 1) h) (readProbe f p w) = readProbe f q w := by
  cases h
  rfl

variable {V E : Type} [Fintype V] [Fintype E]
variable (G : Graph V E) (p : ThreePorts G) (f : ℤ[X]) (s : V → Bool)
local notation "S₀" => (printedParams (f:=f) (ell:=1) (rootSize V))
local notation "r₀" => originCall G p f s

def printedProbeChart : Fin (probeCount V) ≃ Probe S₀ r₀ :=
  finCongr (printedRootProbeCount_exact G p f s).symm

theorem native_probe_word_is_same (d : Ready S₀ (sourceDelta (rootSize V)) r₀)
    (fit : probeCount V≤2^f.natDegree) (t : Site V) (j : Fin (probeCount V)) :
    NativeProbeRing.chosenRep f.natDegree
      (J9PrintedSchedule.probeCount (r₀).edges (2^(S₀).levelBits (r₀).depth)) d.fit
      (printedProbeChart G p f s j) =
      (exteriorRoster (f:=f) fit).word t j :=
  chosenRep_finCongr f.natDegree (printedRootProbeCount_exact G p f s).symm fit d.fit j

theorem native_root_sample_is_same (d : Ready S₀ (sourceDelta (rootSize V)) r₀)
    (fit : probeCount V≤2^f.natDegree) (t : Site V) (j : Fin (probeCount V)) :
    cast (congrArg (Residue f 1) (printedCenterChart_preserves_precision G p f s t))
      (sampleNode S₀ f 1 r₀ d.fit (printedCenterChart G p f s t) (printedProbeChart G p f s j)) =
      readProbe f (high t) ((exteriorRoster (f:=f) fit).word t j) := by
  change cast (congrArg (Residue f 1) (printedCenterChart_preserves_precision G p f s t))
    (readProbe f _ (NativeProbeRing.chosenRep f.natDegree
      (J9PrintedSchedule.probeCount (r₀).edges (2^(S₀).levelBits (r₀).depth)) d.fit
      (printedProbeChart G p f s j))) = _
  rw [native_probe_word_is_same G p f s d fit t j]
  exact readProbe_transport f (printedCenterChart_preserves_precision G p f s t) _

#print axioms printedProbeChart
#print axioms native_probe_word_is_same
#print axioms native_root_sample_is_same
end
end V8R45PooledLiteral