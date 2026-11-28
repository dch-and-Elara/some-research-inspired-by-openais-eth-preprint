
import J9R20SameFilePublicWorld
import J7LiteralGraphNative

/-! Actual triangle-replacement incidence, not a supplied end atlas.
The printed recursion's existing RootBounds guard implies the separate
large-enough root inequalities used by the source seat construction. -/
namespace J9R20SameFile
open scoped Polynomial Classical
open Polynomial J1PPrinted J6R12Blueprint NativeProbeRing
open J7PrintedParams J7SourceLabels J7LiteralGraph
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3800000

private theorem abstract_pow_lt_of_clog (s n : ℕ) (h : n < Nat.clog 2 s) : (2:ℕ)^n<s :=
  (Nat.lt_clog_iff_pow_lt (by decide : 1<(2:ℕ))).1 h

theorem root_bounds_force_j9_range (s : ℕ) (f : ℤ[X]) (cfg : RootBounds s 3 f) :
    0<f.natDegree ∧ 2^(9*131072-1)<s := by
  have cut : 9*131072-1 < Nat.clog 2 s :=
    lt_of_lt_of_le (by decide : 9*131072-1 < (2*epsDen)^30*3^10) cfg.size
  have pos : 0 < Nat.clog 2 s := lt_trans (by decide : 0<9*131072-1) cut
  refine ⟨?_,abstract_pow_lt_of_clog s _ cut⟩
  rw [cfg.coefficient]
  exact Nat.mul_pos (by decide) pos

/-- Exact printed fixed-layout, fixed-address J9 for original simple
cubic input via the computed triangle-replacement atlas. -/
theorem cubic_graph_public_J9
    {V : Type} [LinearOrder V] [Fintype V] (B : SimpleGraph V) [DecidableRel B.Adj]
    (cubic : Cubic B) (f : ℤ[X]) (ell created : ℕ)
    (hf : f.Monic) (hℓ : 0<ell) (hc : 0<created)
    (cfg : RootBounds (sourceSize (Fintype.card (Pin (Edge B)))) 3 f)
    [Fact (Irreducible (residuePoly f))] :
    ∃ copies : ℕ,
      ∃ geom : SourceGeometry (atlas B cubic)
        (stepA (Nat.clog 2 (sourceSize (Fintype.card (Pin (Edge B))))) 0) copies,
          OriginalPublicWorld (atlas B cubic) f ell created geom hf hℓ := by
  have range := root_bounds_force_j9_range _ f cfg
  exact original_four_clone_graph_public_J9 (atlas B cubic) f ell created hf hℓ range.1 hc range.2 cfg

#print axioms root_bounds_force_j9_range
#print axioms cubic_graph_public_J9
end
end J9R20SameFile
