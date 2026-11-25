import AffineEdgeEncoder
import AffineEdgeOrbitZero
import AffineEdgeOrbitBoundary
import AffineEdgeOrbitCompare
import TernaryCode

open scoped Polynomial

namespace AffineEdge.Orbit

theorem zero_encoder_ratio {q : ℕ} (sites : Fin q → ℚ) (hq : 1 ≤ q) :
    ((zeroEncoder (F := ℚ) q (Fin 2)).rank : ℝ) /
        ((Reconstruction.TernaryCode.encoder q).rank : ℝ) =
      3*(2:ℝ)^q/(2*((2:ℝ)^q+1)) := by
  rw [zeroEncoder_rank q 2 sites, Reconstruction.TernaryCode.encoder_rank]
  exact zero_rank_ratio q hq

theorem boundary_encoder_ratio {q : ℕ} {F : Type*} [Field F] (sites : Fin q → F)
    (hq : 2 ≤ q) (hi : Function.Injective sites) (hn : ∀ t, sites t ≠ 0) :
    ((boundaryEncoder (F := F) q).rank : ℝ) / ((binaryEncoder (F := F) q).rank : ℝ) =
      boundaryRatio q := by
  rw [(boundaryEncoder_attains sites hq hi hn).2, (binaryEncoder_attains sites hq hi hn).2]
  rfl

theorem zero_optimal_needs_coupling {q : ℕ} {I : Type*} [Fintype I]
    {sites : Fin q → ℚ} {C : Matrix I (PairWord q (Fin 2)) ℚ}
    {P : PairWord q (Fin 2) → PairWord q (Fin 2) → ℚ[X]}
    (hq : 2 ≤ q) (hP : PairedCondition sites C 0 P) (hr : C.rank = (4^q-1)/3) :
    ¬ Orbitwise C := by
  intro ho
  have h := orbitwise_zero_rank_lower ho hP
  rw [representative_card, hr] at h
  exact (Nat.not_le.mpr (zero_rank_strict q hq)) h

theorem boundary_optimal_needs_coupling {q : ℕ} {I F : Type*} [Fintype I] [Field F]
    {sites : Fin q → F} {C : Matrix I (Word q) F} {P : Word q → Word q → F[X]}
    (hq : 2 ≤ q) (hi : Function.Injective sites) (hP : PairedCondition sites C (q-2) P)
    (hr : C.rank = q+(q+1)/2+2) :
    ¬ Orbitwise C := by
  intro ho
  have h := orbitwise_boundary_rank_lower hq hi ho hP
  rw [hr] at h
  exact (Nat.not_le.mpr (boundary_rank_strict q hq)) h

end AffineEdge.Orbit
