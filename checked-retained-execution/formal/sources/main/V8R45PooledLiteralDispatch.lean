import V8R45PooledLiteralOrigin
import J6R12BlueprintReach

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
set_option maxRecDepth 2400

/-! Physical child requests for the same high mode and binary word. The
source does not rerun these children at low precision. -/
namespace V8R45PooledLiteral
open scoped BigOperators Classical Polynomial
open Polynomial V8PooledRange V8PooledRange.NativeOrigin
open V8PooledMenu.FiveCopy
open J6R10Repack J6R9Recursive J6R11Blueprint J6R11Repack J6R12Blueprint
open P11FullPacking J6R9PacketScopes

noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]
variable {G : Graph V E} {p : ThreePorts G} {f : ℤ[X]}
variable (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)

def exteriorRoster (fit : probeCount V ≤ 2^f.natDegree) : Probes V f where
  word := fun _ => NativeProbeRing.chosenRep f.natDegree (probeCount V) fit
  distinct := fun _ => NativeProbeRing.chosenRep_injective _ _ _

omit [Fintype E] in
theorem exact_high_mode_menu (t : Site V)
    (β : Mode (rootIndex hu huM t) (high t) P.mask →₀ ℕ) :
    β ∈ J6RecursiveMenu.menu (high t)
      (J6R10RowAffine.weight (rootIndex hu huM t) (high t) P.mask) ↔
    J6RecursiveMenu.weighted (J6R10RowAffine.weight (rootIndex hu huM t) (high t) P.mask) β < high t :=
  J6RecursiveMenu.exact_printed_menu _ _ (fun m => m.order.val.succ_pos) _

def exteriorChild (W : Probes V f) (s : V → Bool) (t : Site V)
    (q : Address P hu huM t) (g : Fin 64) : J6ActiveRun.Call (PhysicalHost f 1) :=
  let host := actualPacketHost P (rootIndex hu huM t) (nonzero_site hu huM t)
    (rootIndex_val hu huM t) (high t) (J6R10Integral.box_two_nil (high t) f 1)
    (readProbe f (high t) (W.word t q.probeIdx)) (file f G p s) q.beta g
  ⟨host,1,host.edgeCount,high t⟩

theorem exterior_child_return_precision (W : Probes V f) (s : V → Bool)
    (t : Site V) (q : Address P hu huM t) (g : Fin 64) :
    (exteriorChild P hu huM W s t q g).prec = high t := rfl


#print axioms exteriorRoster
#print axioms exact_high_mode_menu
#print axioms exteriorChild
#print axioms exterior_child_return_precision
end
end V8R45PooledLiteral