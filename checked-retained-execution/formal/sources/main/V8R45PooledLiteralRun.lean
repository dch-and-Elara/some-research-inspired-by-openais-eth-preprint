import V8R45PooledLiteralGuards
import V8R45PooledLiteralDegree
import V8R45PooledLiteralCallRun
import J6R12RepackReadNatural

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5600000
set_option maxRecDepth 3000

/-! Derive actual child well-formedness from the root incidence and the
same supplied legal packing. The source solver is run at the printed
high precisions; its final integer readout is independently the C6 count. -/
namespace V8R45PooledLiteral
open scoped BigOperators Classical Polynomial
open Polynomial V8PooledRange V8PooledRange.NativeOrigin V8PooledMenu.FiveCopy
open P11FullPacking J6R10Repack J6R11Repack J6R11Blueprint J6R12Blueprint
open J6R9Recursive J6R12Repack J1PPrinted

noncomputable section

variable {V E : Type} [Fintype V] [Fintype E]
variable {G : Graph V E} {p : ThreePorts G} {f : ℤ[X]}

variable (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)

theorem exterior_run_exact_high
    (sel : Selector (printedParams (f:=f) (ell:=1) (rootSize V)) (sourceDelta (rootSize V)))
    (W : Probes V f) (hf : f.Monic)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (s : V → Bool) (t : Site V) (q : Address P hu huM t) (g : Fin 64)
    (cfg : RootBounds (rootSize V) 3 f) :
    exteriorRun P hu huM sel W hf s t q g =
      reduce (high t) f 1 ((exteriorChild P hu huM W s t q g).host.contract hf) :=
  exterior_run_exact_receives P hu huM sel W hf (printed_root_coefficient_positive V cfg)
    s t q g cfg (legal_exterior_children_stable P hu huM W s t q g)

theorem printed_full_run_reads_exact_CNF (G : Graph V E) (p : ThreePorts G)
    (cfg : RootBounds (rootSize V) 3 f) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (sel : Selector (printedParams (f:=f) (ell:=1) (rootSize V)) (sourceDelta (rootSize V)))
    (hu : 0<rootU V) (hf : f.Monic) (s : V → Bool) :
    boxNatural f 1 (originCall G p f s).prec hf
      (@nativePrintedRun f 1 (rootSize V) sel (originCall G p f s) hf) =
      satCount G p s := by
  have hd := printed_root_coefficient_positive V cfg
  rw [native_printed_run_exact sel _ hf hd cfg (literal_root_stable G p f hu s)]
  change boxNatural f 1 (rootPrec V) hf
    (reduce (rootPrec V) f 1 ((rawHost G p f s).contract hf)) = _
  rw [literal_root_exact_CNF G p f s hf hd,map_natCast]
  exact boxNatural_of_nat f 1 (rootPrec V) hf (rootPrec_pos V) (by decide)
    hd _ (physical_terminal_precision G p s)

#print axioms exterior_run_exact_high
#print axioms printed_full_run_reads_exact_CNF
end
end V8R45PooledLiteral