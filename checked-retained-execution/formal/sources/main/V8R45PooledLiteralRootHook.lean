import V8R45PooledLiteralOrigin
import V8R45PooledLiteralSchedule

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4200000
set_option maxRecDepth 2800

/-! Install the very same sign-independent C4 packing at the true root
of the source selector, and identify its coordinate carrier. -/
namespace V8R45PooledLiteral
open scoped Classical Polynomial
open Polynomial V8PooledRange V8PooledMenu.FiveCopy
open J6R12Blueprint J6R10Repack J6R11Blueprint J6ActiveRun J1PPrinted

noncomputable section

def useRootPacking {f : ℤ[X]} {ell Δ : ℕ} {S : Params (f:=f) (ell:=ell)}
    (fallback : Selector S Δ) {r : Call (PhysicalHost f ell)}
    (P : PhysicalPacking r.host.network (S.levelBits r.depth) (Fin 64)) : Selector S Δ :=
  fun c d => if h : r = c then h ▸ P else fallback c d

theorem useRootPacking_sends_same {f : ℤ[X]} {ell Δ : ℕ} {S : Params (f:=f) (ell:=ell)}
    (fallback : Selector S Δ) {r : Call (PhysicalHost f ell)}
    (P : PhysicalPacking r.host.network (S.levelBits r.depth) (Fin 64)) (d : Ready S Δ r) :
    packing (useRootPacking fallback P) d = P := by
  simp [packing,useRootPacking]

variable {V E : Type} [Fintype V] [Fintype E]
variable (G : Graph V E) (p : ThreePorts G) (f : ℤ[X]) (s : V → Bool)
local notation "S₀" => (printedParams (f:=f) (ell:=1) (rootSize V))
local notation "r₀" => originCall G p f s

def sourceRootPacking (P : Packing G p) :
    PhysicalPacking (r₀).host.network ((S₀).levelBits (r₀).depth) (Fin 64) :=
  by
    change PhysicalPacking (network G p) (stepA (Nat.clog 2 (rootSize V)) 0) (Fin 64)
    rw [printed_root_bits]
    exact P

def installC4Packing (fallback : Selector S₀ (sourceDelta (rootSize V))) (P : Packing G p) :
    Selector S₀ (sourceDelta (rootSize V)) :=
  useRootPacking fallback (sourceRootPacking G p f s P)

theorem same_C4_packing_selected (fallback : Selector S₀ (sourceDelta (rootSize V)))
    (P : Packing G p) (d : Ready S₀ (sourceDelta (rootSize V)) r₀) :
    packing (installC4Packing G p f s fallback P) d = sourceRootPacking G p f s P :=
  useRootPacking_sends_same fallback (sourceRootPacking G p f s P) d

def printedCenterChart : Site V ≃ J6ActiveRun.Center S₀ r₀ :=
  Equiv.subtypeEquivRight (fun t => by
    change t ∈ J6ActiveSchedule.active (rootA V) (wireSize V) (rootU V) ↔
      t ∈ J6ActiveSchedule.active (stepA (Nat.clog 2 (rootSize V)) 0) (wireSize V)
        (stepU (Nat.clog 2 (rootSize V)) 0)
    rw [printed_root_bits,printed_root_width])

theorem printedCenterChart_preserves_signed_center (t : Site V) :
    (printedCenterChart G p f s t).val = t.val := rfl

theorem printedCenterChart_preserves_precision (t : Site V) :
    registerPrecision S₀ r₀ (printedCenterChart G p f s t) = high t :=
  (printed_site_precision V t).symm

theorem printedCenterChart_preserves_index (hu : 0<rootU V) (huM : rootU V≤wireSize V)
    (d : Ready S₀ (sourceDelta (rootSize V)) r₀) (t : Site V) :
    (centerIndex d (printedCenterChart G p f s t)).val = (rootIndex hu huM t).val := rfl

theorem printedRootProbeCount_exact :
    J9PrintedSchedule.probeCount (r₀).edges (2^(S₀).levelBits (r₀).depth) = probeCount V := by
  change J9PrintedSchedule.probeCount (wireSize V)
    (2^stepA (Nat.clog 2 (rootSize V)) 0) = _
  rw [printed_root_bits]; rfl

#print axioms useRootPacking_sends_same
#print axioms same_C4_packing_selected
#print axioms printedCenterChart
#print axioms printedCenterChart_preserves_signed_center
#print axioms printedCenterChart_preserves_precision
#print axioms printedCenterChart_preserves_index
#print axioms printedRootProbeCount_exact
end
end V8R45PooledLiteral