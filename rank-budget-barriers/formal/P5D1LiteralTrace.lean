import P5D1LiteralRank
import FixedSchedule

/-! Lowering to cost needs a paid materialization trace. A fixed agenda
does not identify a common left/right local family across unrelated cuts. -/
namespace Paper5.D1Literal
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R11Repack J6R11Blueprint J6ActiveRun
  J6R12Blueprint J6R10Reachable J6R9Recursive J6R9PacketScopes
  P11FullPacking Paper5.HybridClosure J1PPrinted J6R12Integral SeparatedRank

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W × W)) (cubic : ∀ v, GraphCutMoments.degree F v=3)
variable (f : ℤ[X])
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "Δ" => sourceDelta (oldRowSize F)
local notation "r*" => (oldRowRoot F cubic f (fun _ => false))
variable (P : RootPacking F cubic f)

theorem separately_paid_literal_root {I : Type} [Fintype I] [DecidableEq I]
    (cfg : RootBounds (oldRowSize F) 3 f) (hΔ : 3 ≤ Δ)
    (hf : f.Monic) (hF : 0 < f.natDegree) [Fact (Irreducible (NativeProbeRing.residuePoly f))]
    (d : Ready S Δ r*) (matching : PinnedCNF.InducedMatching F I)
    (symbols : rootKept F f → Finset (Fin 64))
    (D : ℕ) (small : D ≤ Fintype.card I)
    (gap : ∀ i, D ≤ endpointImbalance matching.endpoint
      (EmpiricalCutMoments.labelCut (rootLabels F cubic f P) id symbols i))
    (trace : FixedSchedule.Execution (PublicSlot F cubic f P d)) :
    2^D ≤ trace.cost :=
  (literal_menu_card_from_matching F cubic f P cfg hΔ hf hF d matching symbols D small gap).trans
    (FixedSchedule.card_le_cost trace)

/-- Even under exact uniform support on a product of two coordinates,
a cut determined by each coordinate separately can only be trivial.
This prevents deducing any common cut from fixed public addresses. -/
theorem two_coordinate_common_cut_constant {A B : Type*} (side : A × B → Bool)
    (first : A → Bool) (second : B → Bool)
    (h₁ : ∀ p, side p=first p.1) (h₂ : ∀ p, side p=second p.2) :
    ∀ p q, side p=side q := by
  intro p q
  calc
    side p = first p.1 := h₁ p
    _ = side (p.1,q.2) := (h₁ (p.1,q.2)).symm
    _ = second q.2 := h₂ (p.1,q.2)
    _ = side q := (h₂ q).symm

#print axioms separately_paid_literal_root
#print axioms two_coordinate_common_cut_constant
end Paper5.D1Literal
