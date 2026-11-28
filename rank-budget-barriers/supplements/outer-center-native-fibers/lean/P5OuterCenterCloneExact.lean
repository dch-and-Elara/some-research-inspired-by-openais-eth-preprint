import P5OuterCenterGraph
import P5D1LiteralRoot
import P5HybridDUnclonedParams

set_option warningAsError true
namespace Paper5.OuterCenters.Cloned
open scoped BigOperators Classical Polynomial
open P11FullPacking J6R10Repack J6R9PacketScopes HybridClosure D1Literal

variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (cub : ∀ v,GraphCutMoments.degree F v=3)

include cub in
theorem rootBits_small_for_cloned (hn : 0 < Fintype.card W) :
    512 * HybridDUncloned.rootBits (oldRowSize F) < Fintype.card W := by
  have hs := oldRow_size_exact F cub
  have hclog : Nat.clog 2 (oldRowSize F) ≤ oldRowSize F := by
    apply (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).mpr
    exact Nat.le_of_lt Nat.lt_two_pow_self
  have hr := (HybridDUncloned.printed_dimension_words (oldRowSize F)).1
  have hu : HybridDUncloned.rootWidth (oldRowSize F) =
      Nat.clog 2 (oldRowSize F) / 131072 := rfl
  omega

theorem actual_cloned_count_fiber {a : ℕ}
    (P : PhysicalPacking (dNetwork F cub) a (Fin 64))
    (m : W ≃ W) (edge : ∀ x, (x,m x) ∈ F ∨ (m x,x) ∈ F)
    (K : ℕ) (hK : 1024*K ≤ 2^a) (ha : 512*a < Fintype.card W) :
    ∃ x : W,
      let σ : W → Bool := fun _ => true
      let τ := signsWithTwoZero x (m x)
      let CNF := MainClonedCNF.formula F (MainClonedCNF.leftSlot F cub) (MainClonedCNF.rightSlot F cub)
      PinnedCNF.modelCount (CNF σ) = 1 ∧ PinnedCNF.modelCount (CNF τ) = 0 ∧
      ∀ (i : Fin a) (t : ℤ) (ht : t ≠ 0) (hv : padicValInt 2 t = i.val) (p : ℕ)
        (f : ℤ[X]) (hf : f.Monic) (hnil : (2 : Residue f 1 p)^p = 0)
        (β : Mode i p P.mask →₀ ℕ) (g : Fin 64),
        (((2^a : ℕ) : ℤ) - K ≤ t ∨ t ≤ -(((2^a : ℕ) : ℤ) - K)) →
        nativeRead F cub P i ht hv (4*Fintype.card W+1) p f hf hnil σ β g =
        nativeRead F cub P i ht hv (4*Fintype.card W+1) p f hf hnil τ β g := by
  obtain ⟨x,h₁,h₀,hread⟩ := genuine_outer_child_fiber F cub P K m edge
    (budget_from_printed_packets F cub P K hK ha)
  refine ⟨x,?_,?_,?_⟩
  · simpa only [MainClonedCNF.modelCount_cloned] using h₁
  · simpa only [MainClonedCNF.modelCount_cloned] using h₀
  · intro i t ht hv p f hf hnil β g ho
    exact hread i t ht hv _ p f hf hnil β g ho

#print axioms rootBits_small_for_cloned
#print axioms actual_cloned_count_fiber
end Paper5.OuterCenters.Cloned

