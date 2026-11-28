import ColorAlphabetFinite
import ColorAlphabetLower
import Mathlib.SetTheory.Cardinal.Basic

open scoped Polynomial

namespace Reconstruction.ColorAlphabet

/-- A field of cardinality greater than two contains a scalar available for
the second off-diagonal row. -/
theorem exists_scalar_ne_zero_ne_one {F : Type u} [Field F] (hF : 2 < Cardinal.mk F) :
    ∃ x : F, x ≠ 0 ∧ x ≠ 1 := by
  classical
  by_contra! h
  have hc (x : F) : x = 0 ∨ x = 1 := or_iff_not_imp_left.mpr (h x)
  let f (x : F) : ULift.{u} Bool := ⟨decide (x = 1)⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    rcases hc x with rfl | rfl <;> rcases hc y with rfl | rfl <;> simp_all [f]
  have hle := Cardinal.mk_le_of_injective hinj
  exact (not_le_of_gt hF) (by simpa using hle)

/-- The binary degree-zero optimum over any field of cardinality greater than two.
The result holds for all evaluation labels because the matrix is constant. -/
theorem exact_binary_field_minimum {F : Type u} [Field F] (hF : 2 < Cardinal.mk F)
    (q : ℕ) (a : Fin q → F) :
    IsLeast {k : ℕ | ∃ (m : ℕ) (C : Matrix (Fin m) (Word (fun _ : Fin q => Fin 2)) F)
      (P : Matrix (Word (fun _ : Fin q => Fin 2)) (Word (fun _ : Fin q => Fin 2)) F[X]),
      FeasibleZero a C P ∧ C.rank = k} ((4^q-1)/3) := by
  obtain ⟨θ, h0, h1⟩ := exists_scalar_ne_zero_ne_one hF
  obtain ⟨m, C, P, hP, hm, hu⟩ := binary_field_upper θ h0 h1 q a
  have hl := binary_field_rank_lower q C (feasibleZero_recovers hP)
  refine ⟨⟨m, C, P, hP, Nat.le_antisymm hu hl⟩, ?_⟩
  rintro n ⟨m, N, Q, hQ, rfl⟩
  exact binary_field_rank_lower q N (feasibleZero_recovers hQ)

end Reconstruction.ColorAlphabet
