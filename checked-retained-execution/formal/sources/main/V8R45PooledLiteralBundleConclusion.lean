import V8R45PooledLiteralMenu

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4100000
set_option maxRecDepth 2700

/-! One typed record binds the same fixed C6 graph and legal C4 chart. -/
namespace V8R45PooledLiteral
open scoped Classical Polynomial
open Polynomial V8PooledRange V8PooledRange.NativeOrigin V8PooledMenu.FiveCopy
open J6R12Blueprint J1PPrinted
noncomputable section

structure PooledInput {k : ℕ} {E : Type} [Fintype E]
    (H : Graph (Deficit k) E) (p : ThreePorts H) (f : ℤ[X]) where
  packing : Packing (Split.graph H p) (Split.ports H p)
  active : 0<rootU (Split.V k)
  sel : Selector (printedParams (f:=f) (ell:=1) (rootSize (Split.V k)))
    (sourceDelta (rootSize (Split.V k)))
  probes : Probes (Split.V k) f
  monic : f.Monic
  cap : PublicPrecision (Split.V k)
  bounds : RootBounds (rootSize (Split.V k)) 3 f

namespace PooledInput
variable {k : ℕ} {E : Type} [Fintype E] {H : Graph (Deficit k) E} {p : ThreePorts H} {f : ℤ[X]}
variable (I : PooledInput H p f)

abbrev Menu :=
  WholeMenu f I.packing I.active (V8PooledMenu.rootU_fits (Split.V k)) I.cap
def computed : (Split.V k → Bool) → I.Menu :=
  realMenu I.packing I.active (V8PooledMenu.rootU_fits (Split.V k)) I.sel I.probes I.monic I.cap
def prior : (Split.V k → Bool) → I.Menu :=
  nativeMenu I.packing I.active (V8PooledMenu.rootU_fits (Split.V k)) I.cap I.probes I.monic
def bits : ℕ := V8PooledMenu.pooledBits (rootA (Split.V k)) (rootU (Split.V k)) I.cap.prec
def target (_I : PooledInput H p f) : (Split.V k → Bool) → ℕ :=
  satCount (Split.graph H p) (Split.ports H p)

private theorem side_named_eq {M : Type*} (Side : M→Type*) {a b : M}
    (h : a=b) (x : Side a) : (⟨b,cast (congrArg Side h) x⟩ : Sigma Side) = ⟨a,x⟩ := by
  cases h
  rfl

variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

theorem same_computed_menu (s : Split.V k → Bool) : I.computed s = I.prior s :=
  real_receiving_menu_is_C4 I.packing I.active (V8PooledMenu.rootU_fits (Split.V k))
    I.sel I.probes I.monic I.bounds I.cap s

theorem exact_dependent_decoder_from_exterior_runs (b : ℕ)
    (Side : I.Menu → Type*) [∀ m, Fintype (Side m)]
    (hSide : ∀ m, Fintype.card (Side m) ≤ 2^b)
    (aux : ∀ s, Side (I.computed s)) (dec : Sigma Side → ℕ)
    (correct : ∀ s, dec ⟨I.computed s,aux s⟩ = I.target s) :
    ((Fintype.card (Split.V k) : ℚ)-10)/12 ≤ ((I.bits+b : ℕ) : ℚ) := by
  let aux' (s : Split.V k → Bool) : Side (I.prior s) :=
    cast (congrArg Side (I.same_computed_menu s)) (aux s)
  refine V8PooledMenu.actual_pooled_decoder H p I.packing I.active
    (V8PooledMenu.rootU_fits (Split.V k)) I.cap I.probes I.monic
    (printed_root_coefficient_positive (Split.V k) I.bounds) b Side hSide aux' dec ?_
  intro s
  exact (congrArg dec (side_named_eq Side (I.same_computed_menu s) (aux s))).trans
    ((correct s).trans (originCount_eq (Split.graph H p) (Split.ports H p) s).symm)

theorem same_literal_inputs_exclude_menu_only (dec : I.Menu → ℕ) :
    ∃ s : Split.V k → Bool, dec (I.computed s) ≠ I.target s := by
  apply not_forall.mp
  intro ht
  apply V8PooledMenu.no_menu_only_decoder H p I.packing I.active
    (V8PooledMenu.rootU_fits (Split.V k)) I.cap I.probes I.monic
    (printed_root_coefficient_positive (Split.V k) I.bounds) dec
  intro s
  exact ((congrArg dec (I.same_computed_menu s)).symm.trans (ht s)).trans
    (originCount_eq (Split.graph H p) (Split.ports H p) s).symm

theorem original_C4_C6_same_graph (hs : IsSimple H) (γ : ℚ) (hγ : 0≤γ) (he : Split.Expansion H γ) :
    Split.C6Certificate H p γ ∧
    Nat.card (Set.range I.computed) ≤ 2^I.bits ∧
    I.bits < (2*2^rootA (Split.V k))*V8PooledMenu.triangle (rootA (Split.V k)+1) ∧
    ∀ dec : I.Menu→ℕ, ∃ s : Split.V k→Bool, dec (I.computed s) ≠ I.target s :=
  ⟨Split.c6_certificate H p hs γ hγ he,
   real_menu_capacity_C4 I.packing I.active (V8PooledMenu.rootU_fits (Split.V k))
     I.sel I.probes I.monic I.bounds I.cap,
   source_C4_strict I.cap, I.same_literal_inputs_exclude_menu_only⟩

#print axioms same_computed_menu
#print axioms exact_dependent_decoder_from_exterior_runs
#print axioms same_literal_inputs_exclude_menu_only
#print axioms original_C4_C6_same_graph
end PooledInput
end
end V8R45PooledLiteral