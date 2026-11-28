import V8R45PooledLiteralBundleConclusion
import V8R45PooledLiteralChoosePacking
import V8R45PooledLiteralRun

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000
set_option maxRecDepth 2700

/-! A concrete graph-only layout and canonical roster for the exact same
input family. This is existence and semantics, not acquisition cost. -/
namespace V8R45PooledLiteral.PooledInput
open scoped Classical Polynomial
open Polynomial V8PooledRange V8PooledMenu.FiveCopy
open J6R12Blueprint J6R12Repack J1PPrinted
noncomputable section

variable {k : ℕ} {E : Type} [Fintype E] (H : Graph (Deficit k) E) (p : ThreePorts H) {f : ℤ[X]}

def canonical (cfg : RootBounds (rootSize (Split.V k)) 3 f)
    (hf : f.Monic) (L : PublicPrecision (Split.V k)) : PooledInput H p f where
  packing := oneGraphOnlyPacking (Split.graph H p) (Split.ports H p) cfg.widthPos
  active := cfg.widthPos
  sel := defaultSelector (printedParams (rootSize (Split.V k))) (sourceDelta (rootSize (Split.V k)))
  probes := exteriorRoster (f:=f) (printed_root_coefficient_count (Split.V k) cfg)
  monic := hf
  cap := L
  bounds := cfg

variable {H p}

theorem full_native_count_on_same_installed_root (I : PooledInput H p f)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (s : Split.V k → Bool) :
    let r := originCall (Split.graph H p) (Split.ports H p) f s
    let selected := installC4Packing (Split.graph H p) (Split.ports H p) f s I.sel I.packing
    boxNatural f 1 r.prec I.monic
      (@nativePrintedRun f 1 (rootSize (Split.V k)) selected r I.monic) = I.target s :=
  printed_full_run_reads_exact_CNF (Split.graph H p) (Split.ports H p)
    I.bounds (installC4Packing (Split.graph H p) (Split.ports H p) f s I.sel I.packing)
    I.active I.monic s

theorem no_decoder_on_graph_only_canonical
    (cfg : RootBounds (rootSize (Split.V k)) 3 f)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (hf : f.Monic) (L : PublicPrecision (Split.V k))
    (D : (canonical H p cfg hf L).Menu → ℕ) :
    ∃ s : Split.V k → Bool, D ((canonical H p cfg hf L).computed s) ≠
      satCount (Split.graph H p) (Split.ports H p) s :=
  (canonical H p cfg hf L).same_literal_inputs_exclude_menu_only D

#print axioms full_native_count_on_same_installed_root
#print axioms no_decoder_on_graph_only_canonical
end
end V8R45PooledLiteral.PooledInput