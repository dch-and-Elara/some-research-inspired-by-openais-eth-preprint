import P5D1LiteralPrinted

/-! The stronger numerical source-replay guard is eventual too, on the
same actual E1 family. This combines existing schedule asymptotics, not
a new graph existence theorem. -/
namespace Paper5.D1Literal
open scoped Topology
open Filter J1PPrinted Paper5.HybridClosure.Printed

theorem original_D1_numeric_eventual (γ : ℚ) (hγ : 0 < γ) :
    ∀ᶠ N : ℕ in atTop, Ready γ N ∧ (2*epsDen)^30*(3:ℕ)^10 ≤ dLambda N := by
  have hclog : Tendsto (Nat.clog 2) atTop atTop := by
    simpa only [one_mul,add_zero] using clog_linear_tendsto 1 0 (by decide)
  filter_upwards [actual_printed_eventual_ready γ hγ,
    hclog.eventually (eventually_ge_atTop ((2*epsDen)^30*(3:ℕ)^10))] with N hR hN
  exact ⟨hR,hN.trans (Nat.clog_mono_right 2 (d_size_bounds N).1)⟩

theorem original_D1_size_threshold (γ : ℚ) (hγ : 0 < γ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, Ready γ N ∧ (2*epsDen)^30*(3:ℕ)^10 ≤ dLambda N :=
  eventually_atTop.1 (original_D1_numeric_eventual γ hγ)

#print axioms original_D1_numeric_eventual
#print axioms original_D1_size_threshold
end Paper5.D1Literal
