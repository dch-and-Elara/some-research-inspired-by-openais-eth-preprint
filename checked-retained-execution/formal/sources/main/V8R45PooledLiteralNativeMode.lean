import V8R45PooledLiteralRootProbe
import V8R45PooledLiteralPacketTransport
import V8R45PooledLiteralChartCoherence

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000
set_option maxRecDepth 3000

namespace V8R45PooledLiteral
open scoped Classical Polynomial
open Polynomial V8PooledRange V8PooledMenu.FiveCopy
open J6R12Blueprint J6R9Recursive J6R10Repack J6ActiveRun J1PPrinted
open J6R9PacketScopes P11FullPacking J6R10Reachable J6R11Blueprint
noncomputable section

structure CanonicalFrame {V E : Type} [Fintype V] [Fintype E]
    (G : Graph V E) (p : ThreePorts G) (f : ℤ[X]) where
  sign : V → Bool
  fallback : Selector (printedParams (f:=f) (ell:=1) (rootSize V)) (sourceDelta (rootSize V))
  pack : Packing G p
  ready : Ready (printedParams (f:=f) (ell:=1) (rootSize V))
    (sourceDelta (rootSize V)) (originCall G p f sign)
  positive : 0<rootU V
  fitU : rootU V≤wireSize V

namespace CanonicalFrame
variable {V E : Type} [Fintype V] [Fintype E] {G : Graph V E} {p : ThreePorts G} {f : ℤ[X]}
variable (C : CanonicalFrame G p f)

abbrev r := originCall G p f C.sign
abbrev sel := installC4Packing G p f C.sign C.fallback C.pack
abbrev site := printedCenterChart G p f C.sign
abbrev prec (t : Site V) :=
  registerPrecision (printedParams (f:=f) (ell:=1) (rootSize V)) C.r (C.site t)

def bitsEq (V : Type) [Fintype V] : rootA V = stepA (Nat.clog 2 (rootSize V)) 0 :=
  (printed_root_bits V).symm

theorem precEq (t : Site V) : high t = C.prec t :=
  (printedCenterChart_preserves_precision G p f C.sign t).symm

theorem installed_root_packing_is_reindexed :
    movePacking (N:=network G p) (bitsEq V) C.pack =
      J6R12Blueprint.packing C.sel C.ready := by
  change sourceRootPacking G p f C.sign C.pack = J6R12Blueprint.packing C.sel C.ready
  exact (same_C4_packing_selected G p f C.sign C.fallback C.pack C.ready).symm

theorem reindexed_root_ordinal (t : Site V) :
    Fin.cast (bitsEq V) (rootIndex C.positive C.fitU t) =
      J6R12Blueprint.centerIndex C.ready (C.site t) :=
  Fin.ext (printedCenterChart_preserves_index G p f C.sign C.positive C.fitU C.ready t).symm

def normalizedSourceMode (t : Site V) (q : V8PooledMenu.FiveCopy.Address C.pack C.positive C.fitU t) :
    J6R12Integral.LiteralMenu C.sel C.ready (C.site t) := by
  let i := rootIndex C.positive C.fitU t
  let a₁ : Mode (Fin.cast (bitsEq V) i) (C.prec t) (movePacking (bitsEq V) C.pack).mask →₀ ℕ :=
    Finsupp.embDomain (moveMode (bitsEq V) (C.precEq t) C.pack i).toEmbedding q.beta
  let qβ : SiteMode C.sel C.ready (C.site t) →₀ ℕ :=
    Finsupp.embDomain (alignMode C.installed_root_packing_is_reindexed
       (C.reindexed_root_ordinal t)).toEmbedding a₁
  have h₁ := (same_mode_mem_after_transport (bitsEq V) (C.precEq t) C.pack i q.beta).mpr q.legal
  have h₂ : qβ ∈ J6RecursiveMenu.menu (C.prec t) (siteWeight C.sel C.ready (C.site t)) :=
    (align_mode_keeps_menu C.installed_root_packing_is_reindexed
      (C.reindexed_root_ordinal t) a₁).mpr h₁
  exact ⟨qβ,h₂⟩

def sourceNativeAddress (t : Site V) (q : V8PooledMenu.FiveCopy.Address C.pack C.positive C.fitU t)
    (g : Fin 64) :
    NativeAddress (shape (printedParams (rootSize V)) (sourceDelta (rootSize V)) C.sel) C.r :=
  ⟨C.site t,printedProbeChart G p f C.sign q.probeIdx,
    (J6R12Integral.siteMenuEquiv C.sel C.ready (C.site t)).symm
      (C.normalizedSourceMode t q),g⟩

theorem source_native_address_recovers_mode (t : Site V)
    (q : V8PooledMenu.FiveCopy.Address C.pack C.positive C.fitU t) (g : Fin 64) :
    siteTuple C.sel C.ready (C.sourceNativeAddress t q g) = (C.normalizedSourceMode t q).val := by
  let x := C.normalizedSourceMode t q
  let e := J6R12Integral.siteMenuEquiv C.sel C.ready (C.site t)
  have h := J6R12Integral.siteMenuEquiv_tuple C.sel C.ready (C.site t)
    (printedProbeChart G p f C.sign q.probeIdx) (e.symm x) g
  change (e (e.symm x)).val = siteTuple C.sel C.ready (C.sourceNativeAddress t q g) at h
  exact h.symm.trans (congrArg Subtype.val (e.apply_symm_apply x))

#print axioms installed_root_packing_is_reindexed
#print axioms reindexed_root_ordinal
#print axioms normalizedSourceMode
#print axioms source_native_address_recovers_mode
end CanonicalFrame

end
end V8R45PooledLiteral