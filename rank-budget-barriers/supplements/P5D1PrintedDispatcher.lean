import P5D1LiteralPrinted

/-! Exact §11 entry predicate, from frozen quantitative-reduction.tex
362–369. This module checks dispatch on the raw cloned CNF; it certifies
neither an alternative containment preprocessor nor its runtime. -/
namespace Paper5.D1Literal
open scoped Classical
open GraphCutMoments Paper5.HybridClosure
open Paper5.HybridClosure.Printed
set_option autoImplicit false
set_option warningAsError true

/-- The combined source chooses the clause network exactly when this predicate
holds (otherwise it uses the parity queries). Both logarithms are ceilings. -/
def sourceClauseNetworkBranch (n m : ℕ) : Prop :=
  m ≤ n * Nat.clog 2 (Nat.clog 2 n)

theorem cloned_source_clause_network_branch_iff (N : ℕ) (hN : 0 < N) :
    sourceClauseNetworkBranch (4*N) (5*N+3*N/2) ↔ 2 ≤ N := by
  let v := Nat.clog 2 (Nat.clog 2 (4*N))
  change 5*N+3*N/2 ≤ (4*N)*v ↔ 2≤N
  have hlog : 2 ≤ v ↔ 2 ≤ N := by
    change 1 < Nat.clog 2 (Nat.clog 2 (4*N)) ↔ 2≤N
    rw [Nat.lt_clog_iff_pow_lt (by decide : 1 < (2:ℕ))]
    have h : 2 < Nat.clog 2 (4*N) ↔ 2^2 < 4*N :=
      Nat.lt_clog_iff_pow_lt (by decide : 1 < (2:ℕ))
    change 2 < Nat.clog 2 (4*N) ↔ 2≤N
    rw [h]
    omega
  constructor
  · intro h
    apply hlog.mp
    by_contra! hv
    have hb : (4*N)*v ≤ (4*N)*1 := Nat.mul_le_mul_left _ (by omega)
    omega
  · intro h
    have hb : (4*N)*2 ≤ (4*N)*v := Nat.mul_le_mul_left _ (hlog.mpr h)
    omega

variable {W : Type} [Fintype W] [DecidableEq W] [Nonempty W]

/-- The dispatch census uses exactly the formula supplying the old-row
network and recovers its actual size parameter. The threshold is in
original graph vertices, not the 4N cloned variables. -/
theorem oldRow_dispatch_matches_cloned_formula (F : Finset (W × W))
    (reg : ∀ v, degree F v = 3) (σ : W→Bool) :
    let n := Fintype.card (Clone W)
    let m := (MainClonedCNF.formula F (MainClonedCNF.leftSlot F reg)
      (MainClonedCNF.rightSlot F reg) σ).length
    (sourceClauseNetworkBranch n m ↔ 2 ≤ Fintype.card W) ∧
      n + m = oldRowSize F := by
  dsimp only
  refine ⟨?_, ?_⟩
  · rw [cloned_clause_count, Fintype.card_prod, Fintype.card_fin]
    have he := regular_edge_count F 3 reg
    have hcard : F.card = 3 * Fintype.card W / 2 := by omega
    rw [hcard, Nat.mul_comm (Fintype.card W) 4]
    exact cloned_source_clause_network_branch_iff _ Fintype.card_pos
  · rw [d_size_is_cloned F reg σ, oldRowSize_eq_dSize F reg]

#print axioms cloned_source_clause_network_branch_iff
#print axioms oldRow_dispatch_matches_cloned_formula

/-- On every nonempty cubic graph the raw cloned formula reaches the actual
network branch. No size guard on the subsequent contraction is asserted. -/
theorem oldRow_dispatch_selects_clause_network (F : Finset (W × W))
    (reg : ∀ v, degree F v = 3) (σ : W→Bool) :
    let n := Fintype.card (Clone W)
    let m := (MainClonedCNF.formula F (MainClonedCNF.leftSlot F reg)
      (MainClonedCNF.rightSlot F reg) σ).length
    sourceClauseNetworkBranch n m := by
  have h := regular_edge_count F 3 reg
  have hp : 0 < Fintype.card W := Fintype.card_pos
  have hN : 2 ≤ Fintype.card W := by omega
  exact ((oldRow_dispatch_matches_cloned_formula F reg σ).1).mpr hN

#print axioms oldRow_dispatch_selects_clause_network
end Paper5.D1Literal
