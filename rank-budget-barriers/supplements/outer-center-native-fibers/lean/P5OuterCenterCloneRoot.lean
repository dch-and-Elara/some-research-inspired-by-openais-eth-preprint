import P5OuterCenterCloneExact
import P5OuterCenterCenters

set_option warningAsError true
set_option maxHeartbeats 1500000
namespace Paper5.OuterCenters.Cloned
open scoped BigOperators Classical Polynomial
open P11FullPacking J6R10Repack J6R9PacketScopes HybridDUncloned HybridClosure
  J6ActiveRun J6ActiveSchedule J6R12Blueprint J6R9Recursive P1DyadicGrid J9PrintedSchedule D1Literal

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (cub : ∀ v,GraphCutMoments.degree F v=3)
local notation "NW" => dNetwork F cub

theorem every_source_outer_zero_child
    (mate : W ≃ W) (edge : ∀ x, (x,mate x) ∈ F ∨ (mate x,x) ∈ F)
    (P : PhysicalPacking NW (rootBits (oldRowSize F)) (Fin 64))
    (K : ℕ) (hK : 1024*K ≤ 2^rootBits (oldRowSize F))
    (hn : 0 < Fintype.card (W)) (f : ℤ[X]) (hf : f.Monic)
    (d : Ready (printedParams (f:=f) (ell:=1) (oldRowSize F))
      (J1PPrinted.sourceDelta (oldRowSize F)) (oldRowRoot F cub f (fun _ => true))) :
    let c₀ := oldRowRoot F cub f (fun _ => true)
    let S := printedParams (f:=f) (ell:=1) (oldRowSize F)
    ∃ x : W,
      let σ : W → Bool := fun _ => true
      let τ := signsWithTwoZero x (mate x)
      let CNF := MainClonedCNF.formula F (MainClonedCNF.leftSlot F cub) (MainClonedCNF.rightSlot F cub)
      PinnedCNF.modelCount (CNF σ) = 1 ∧ PinnedCNF.modelCount (CNF τ) = 0 ∧
      ∀ (t : Center S c₀)
        (β : Mode (centerIndex d t) (registerPrecision S c₀ t) P.mask →₀ ℕ)
        (g : Fin 64),
        (((2^rootBits (oldRowSize F) : ℕ) : ℤ) - K ≤ t.val ∨
          t.val ≤ -(((2^rootBits (oldRowSize F) : ℕ) : ℤ) - K)) →
        @nativeRead (W) _ _ F cub (Fin 64) _ _ (rootBits (oldRowSize F)) P (centerIndex d t) t.val (centerNonzero t) rfl c₀.prec
          (registerPrecision S c₀ t) f hf
          (J6R10Integral.box_two_nil (registerPrecision S c₀ t) f 1) σ β g =
        @nativeRead (W) _ _ F cub (Fin 64) _ _ (rootBits (oldRowSize F)) P (centerIndex d t) t.val (centerNonzero t) rfl c₀.prec
          (registerPrecision S c₀ t) f hf
          (J6R10Integral.box_two_nil (registerPrecision S c₀ t) f 1) τ β g := by
  obtain ⟨x,h₁,h₀,hread⟩ := actual_cloned_count_fiber F cub P mate edge K hK
    (rootBits_small_for_cloned F cub hn)
  exact ⟨x,h₁,h₀,fun t β g houter => hread _ t.val (centerNonzero t) rfl _ f hf _ β g houter⟩

#print axioms every_source_outer_zero_child
end Paper5.OuterCenters.Cloned
