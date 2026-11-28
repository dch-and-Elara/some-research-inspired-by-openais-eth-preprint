import P5OuterCenterGraph
import P5OuterCenterCenters

set_option warningAsError true
set_option maxHeartbeats 1500000
namespace Paper5.OuterCenters
open scoped BigOperators Classical Polynomial
open P11FullPacking J6R10Repack J6R9PacketScopes HybridDUncloned HybridClosure
  J6ActiveRun J6ActiveSchedule J6R12Blueprint J6R9Recursive P1DyadicGrid J9PrintedSchedule

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (cub : ∀ v,GraphCutMoments.degree F v=3)
local notation "NW" => HybridDUncloned.network F cub

include cub in
theorem rootBits_small_for_uncloned
    (hn : 0 < Fintype.card W) :
    512 * rootBits (sourceSize F) < Fintype.card W := by
  have hs := (literal_size_bounds F cub).2.1
  have hclog : Nat.clog 2 (sourceSize F) ≤ sourceSize F := by
    apply (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).mpr
    exact Nat.le_of_lt Nat.lt_two_pow_self
  have hr := (printed_dimension_words (sourceSize F)).1
  have hu : rootWidth (sourceSize F) = Nat.clog 2 (sourceSize F) / 131072 := rfl
  omega

theorem every_source_outer_zero_child
    (mate : W ≃ W) (edge : ∀ x, (x,mate x) ∈ F ∨ (mate x,x) ∈ F)
    (P : PhysicalPacking NW (rootBits (sourceSize F)) (Fin 64))
    (K : ℕ) (hK : 1024*K ≤ 2^rootBits (sourceSize F))
    (hn : 0 < Fintype.card (W)) (f : ℤ[X]) (hf : f.Monic)
    (d : Ready (printedParams (f:=f) (ell:=1) (sourceSize F))
      (J1PPrinted.sourceDelta (sourceSize F)) (root F cub f (fun _ => true))) :
    let c₀ := root F cub f (fun _ => true)
    let S := printedParams (f:=f) (ell:=1) (sourceSize F)
    ∃ x : W,
      let σ : W → Bool := fun _ => true
      let τ := signsWithTwoZero x (mate x)
      PinnedCNF.modelCount (PinnedCNF.formula F σ) = 1 ∧
      PinnedCNF.modelCount (PinnedCNF.formula F τ) = 0 ∧
      ∀ (t : Center S c₀)
        (β : Mode (centerIndex d t) (registerPrecision S c₀ t) P.mask →₀ ℕ)
        (g : Fin 64),
        (((2^rootBits (sourceSize F) : ℕ) : ℤ) - K ≤ t.val ∨
          t.val ≤ -(((2^rootBits (sourceSize F) : ℕ) : ℤ) - K)) →
        @nativeRead (W) _ _ F cub (Fin 64) _ _ (rootBits (sourceSize F)) P (centerIndex d t) t.val (centerNonzero t) rfl c₀.prec
          (registerPrecision S c₀ t) f hf
          (J6R10Integral.box_two_nil (registerPrecision S c₀ t) f 1) σ β g =
        @nativeRead (W) _ _ F cub (Fin 64) _ _ (rootBits (sourceSize F)) P (centerIndex d t) t.val (centerNonzero t) rfl c₀.prec
          (registerPrecision S c₀ t) f hf
          (J6R10Integral.box_two_nil (registerPrecision S c₀ t) f 1) τ β g := by
  obtain ⟨x,h₁,h₀,hread⟩ := genuine_outer_child_fiber F cub P K mate edge
    (budget_from_printed_packets F cub P K hK (rootBits_small_for_uncloned F cub hn))
  exact ⟨x,h₁,h₀,fun t β g houter => hread _ t.val (centerNonzero t) rfl _ _ f hf _ β g houter⟩

#print axioms every_source_outer_zero_child
#print axioms rootBits_small_for_uncloned
#print axioms positive_outer_active


end Paper5.OuterCenters







