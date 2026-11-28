import V8R45PooledLiteralGuards
import V8R45PooledLiteralRootHook

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2900000
set_option maxRecDepth 2400

/-! Existence of one graph-only actual layout from the source collision
bounds, not an assertion about an arbitrary input-sensitive tie rule. -/
namespace V8R45PooledLiteral
open scoped Classical Polynomial
open V8PooledRange V8PooledMenu.FiveCopy
open J6R12Blueprint J6R10Repack J6R11Repack P11FullPacking J1PPrinted
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]
variable (G : Graph V E) (p : ThreePorts G)

theorem actual_origin_packing_exists (hu : 0<rootU V) :
    ∃ P : Packing G p, P.copies = ceilCopies (2^rootA V)
      (maxFiber (declaredCell (network G p) P.rowLabel P.colLabel)) := by
  let H := rawHost G p 0 (fun _ => false)
  have d := (literal_root_stable G p 0 hu (fun _ => false)).degree
  have guards := printed_root_packet_guards V hu
  have card : H.edgeCount = wireSize V := literal_root_edgeCount G p 0 (fun _ => false)
  exact host_can_repack H (rootA V) (sourceDelta (rootSize V)) (Fintype.card_fin 64)
    d (by rw [card]; exact guards.1) (by rw [card]; exact guards.2.1)

/-- This witness has no argument carrying a switch word or input file.
The encoding theorem itself still allows every fixed legal packing. -/
def oneGraphOnlyPacking (hu : 0<rootU V) : Packing G p :=
  Classical.choose (actual_origin_packing_exists G p hu)

theorem graph_only_packing_has_source_rounds (hu : 0<rootU V) :
    (oneGraphOnlyPacking G p hu).copies = ceilCopies (2^rootA V)
      (maxFiber (declaredCell (network G p)
        (oneGraphOnlyPacking G p hu).rowLabel (oneGraphOnlyPacking G p hu).colLabel)) :=
  Classical.choose_spec (actual_origin_packing_exists G p hu)

#print axioms actual_origin_packing_exists
#print axioms graph_only_packing_has_source_rounds
end
end V8R45PooledLiteral