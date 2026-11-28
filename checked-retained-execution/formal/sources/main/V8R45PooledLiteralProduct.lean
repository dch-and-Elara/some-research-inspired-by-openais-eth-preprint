import V8R45PooledLiteralRun

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
set_option maxRecDepth 2400

namespace V8R45PooledLiteral
open scoped BigOperators Classical Polynomial
open Polynomial V8PooledRange V8PooledMenu.FiveCopy
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
noncomputable section

def all64 (f : ℤ[X]) (p : ℕ) (a : Fin 64 → Residue f 1 p) : Residue f 1 p :=
  ∏ g, a g

section Slots
variable {V E : Type} [Fintype V] [Fintype E]
variable {G : Graph V E} {p : ThreePorts G} {f : ℤ[X]}
variable (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
variable (sel : Selector (printedParams (f:=f) (ell:=1) (rootSize V)) (sourceDelta (rootSize V)))
variable (W : Probes V f) (hf : f.Monic)

def trueHighProduct (s : V → Bool) (t : Site V) (q : Address P hu huM t) : Residue f 1 (high t) :=
  all64 f (high t) (exteriorRun P hu huM sel W hf s t q)

theorem true_high_product_is_literal (cfg : RootBounds (rootSize V) 3 f)
    [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (s : V → Bool) (t : Site V) (q : Address P hu huM t) :
    trueHighProduct P hu huM sel W hf s t q =
      V8PooledMenu.slot P (rootIndex hu huM t) (nonzero_site hu huM t)
        (rootIndex_val hu huM t) (high t) (J6R10Integral.box_two_nil (high t) f 1)
        (readProbe f (high t) (W.word t q.probeIdx)) (file f G p s) hf q.beta := by
  let word (g : Fin 64) : Residue f 1 (high t) :=
    reduce (high t) f 1 ((exteriorChild P hu huM W s t q g).host.contract hf)
  have h : exteriorRun P hu huM sel W hf s t q = word := by
    funext g
    exact exterior_run_exact_high P hu huM sel W hf s t q g cfg
  exact congrArg (all64 f (high t)) h

#print axioms trueHighProduct
#print axioms true_high_product_is_literal
end Slots
end
end V8R45PooledLiteral