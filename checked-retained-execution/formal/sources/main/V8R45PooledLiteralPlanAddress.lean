import V8R45PooledLiteralNativeMode

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000
set_option maxRecDepth 2600

/-! Exact canonical address and actual Plan child payload before the
separate comparison to the generalized exterior-chart host. -/
namespace V8R45PooledLiteral
open scoped Classical Polynomial
open Polynomial V8PooledRange V8PooledMenu.FiveCopy
open J6R12Blueprint J6R9Recursive J6R10Repack J6ActiveRun J1PPrinted
open J6R9PacketScopes P11FullPacking J6R11Blueprint J6R10Reachable
noncomputable section

namespace CanonicalFrame
variable {V E : Type} [Fintype V] [Fintype E] {G : Graph V E} {p : ThreePorts G} {f : ℤ[X]}
variable (C : CanonicalFrame G p f)

theorem normalized_tuple_exact (t : Site V)
    (q : V8PooledMenu.FiveCopy.Address C.pack C.positive C.fitU t) :
    (C.normalizedSourceMode t q).val =
      Finsupp.embDomain (alignMode (p:=C.prec t) C.installed_root_packing_is_reindexed
        (C.reindexed_root_ordinal t)).toEmbedding
          (Finsupp.embDomain
            (moveMode (bitsEq V) (C.precEq t) C.pack (rootIndex C.positive C.fitU t)).toEmbedding q.beta) :=
  rfl

theorem actual_canonical_plan_child_record (t : Site V)
    (q : V8PooledMenu.FiveCopy.Address C.pack C.positive C.fitU t) (g : Fin 64) :
    let w := C.sourceNativeAddress t q g
    let dest := packetOfSite C.sel C.ready (C.site t) (printedProbeChart G p f C.sign q.probeIdx)
      (C.normalizedSourceMode t q).val g
    (Plan C.sel).child C.r ⟨w,C.ready.active⟩ = ⟨dest,1,dest.edgeCount,C.prec t⟩ := by
  let w := C.sourceNativeAddress t q g
  have h := child_exact C.sel C.ready w
  dsimp only
  change (Plan C.sel).child C.r ⟨w,C.ready.active⟩ = _
  rw [h]
  have hm := C.source_native_address_recovers_mode t q g
  change siteTuple C.sel C.ready w = _ at hm
  rw [hm]
  rfl

#print axioms normalized_tuple_exact
#print axioms actual_canonical_plan_child_record
end CanonicalFrame
end
end V8R45PooledLiteral