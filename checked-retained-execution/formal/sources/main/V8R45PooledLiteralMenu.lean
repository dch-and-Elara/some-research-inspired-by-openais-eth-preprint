import V8R45PooledLiteralGuards
import V8R45PooledLiteralCallRun

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
set_option maxRecDepth 3000

/-! The original C4 channel is the receiving quotient of the entire
64-child product of native calls. No high-mode slot is silently deleted. -/
namespace V8R45PooledLiteral
open scoped BigOperators Classical Polynomial
open Polynomial V8PooledRange V8PooledRange.NativeOrigin V8PooledMenu.FiveCopy
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted

noncomputable section
variable {V E : Type} [Fintype V] [Fintype E]
variable {G : Graph V E} {p : ThreePorts G} {f : ℤ[X]}
variable (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
variable (sel : Selector (printedParams (f:=f) (ell:=1) (rootSize V)) (sourceDelta (rootSize V)))
variable (W : Probes V f) (hf : f.Monic)

def highCompleted (s : V → Bool) (t : Site V) (q : Address P hu huM t) : Residue f 1 (high t) :=
  ∏ g : Fin 64, exteriorRun P hu huM sel W hf s t q g

def realMenu (L : PublicPrecision V) (s : V → Bool) : WholeMenu f P hu huM L :=
  fun t q => V8PooledMenu.observe f (high t) (low hu huM L t) (precision_fits hu huM L t)
    (highCompleted P hu huM sel W hf s t q)

variable (cfg : RootBounds (rootSize V) 3 f)
include cfg
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem high_completed_is_literal (s : V → Bool) (t : Site V) (q : Address P hu huM t) :
    highCompleted P hu huM sel W hf s t q =
      V8PooledMenu.slot P (rootIndex hu huM t) (nonzero_site hu huM t)
        (rootIndex_val hu huM t) (high t) (J6R10Integral.box_two_nil (high t) f 1)
        (readProbe f (high t) (W.word t q.probeIdx)) (file f G p s) hf q.beta := by
  unfold highCompleted V8PooledMenu.slot
  refine Finset.prod_congr rfl fun g _ => ?_
  exact exterior_run_exact_receives P hu huM sel W hf (printed_root_coefficient_positive V cfg)
    s t q g cfg (legal_exterior_children_stable P hu huM W s t q g)

theorem real_receiving_menu_is_C4 (L : PublicPrecision V) (s : V → Bool) :
    realMenu P hu huM sel W hf L s = nativeMenu P hu huM L W hf s := by
  funext t q
  unfold realMenu nativeMenu
  rw [high_completed_is_literal P hu huM sel W hf cfg]

theorem real_menu_factors_through_C4_tape (L : PublicPrecision V) (s : V → Bool) :
    realMenu P hu huM sel W hf L s =
      decodeWhole P hu huM L W (encodeWhole P hu huM L s) := by
  rw [real_receiving_menu_is_C4 P hu huM sel W hf cfg]
  exact nativeMenu_eq P hu huM L W hf (printed_root_coefficient_positive V cfg) s

theorem real_menu_capacity_C4 (L : PublicPrecision V) :
    Nat.card (Set.range (realMenu P hu huM sel W hf L)) ≤
      2^V8PooledMenu.pooledBits (rootA V) (rootU V) L.prec := by
  have h : realMenu P hu huM sel W hf L = nativeMenu P hu huM L W hf :=
    funext (real_receiving_menu_is_C4 P hu huM sel W hf cfg L)
  rw [h]
  exact whole_menu_capacity P hu huM L W hf (printed_root_coefficient_positive V cfg)

theorem complete_nonzero_mode_is_erased (L : PublicPrecision V) (s : V → Bool)
    (t : Site V) (q : Address P hu huM t) (nonzero : q.beta≠0) :
    realMenu P hu huM sel W hf L s t q = 0 := by
  rw [real_menu_factors_through_C4_tape P hu huM sel W hf cfg]
  simp only [decodeWhole,if_neg nonzero]

#print axioms high_completed_is_literal
#print axioms real_receiving_menu_is_C4
#print axioms real_menu_factors_through_C4_tape
#print axioms real_menu_capacity_C4
#print axioms complete_nonzero_mode_is_erased
end

end V8R45PooledLiteral