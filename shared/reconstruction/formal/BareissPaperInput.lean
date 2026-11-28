import BareissPaperGenerate

namespace Reconstruction.BareissPaper

open AffineEdge BareissHeight
open AffineCost.Bit (Run Signed Fraction)
open scoped BigOperators

def scale {q : ℕ} (a : Fin q → Fraction) (e : Equation q) : ℚ :=
  ((a e.1).den.number : ℚ)^(q-2)

private theorem generatedInt_selected {q : ℕ} (a : Fin q → Fraction) (u : Word q)
    (hv : ∀ t, (a t).valid) (e : Equation q) (j : Option (Unknown q)) :
    (generatedInt a u (equationIndex q e) (j.map (unknownIndex q)) : ℚ) =
      scale a e * augment (encoderMatrix (physicalLabels a) u) (encoderRhs u) e j := by
  cases j with
  | none =>
    simpa [generatedInt, scale] using buildEntry_cast a u e none (hv e.1)
  | some j =>
    simpa [generatedInt, scale] using buildEntry_cast a u e (some j) (hv e.1)

/-- Relabeling rows and columns and clearing denominators preserves the
rational solution set. -/
theorem generated_system_iff {q : ℕ} (a : Fin q → Fraction) (u : Word q) (hv : ∀ t, (a t).valid)
    (x : Fin (unknownCount q) → ℚ) :
    (∀ i, (∑ j, (generatedInt a u i (some j) : ℚ) * x j) = (generatedInt a u i none : ℚ)) ↔
      (∀ e, (∑ j, encoderMatrix (physicalLabels a) u e j * decodeSolution x j) =
        encoderRhs u e) := by
  have hsum (e : Equation q) :
      (∑ j, (generatedInt a u (equationIndex q e) (some j) : ℚ) * x j) =
        scale a e * ∑ k, encoderMatrix (physicalLabels a) u e k * decodeSolution x k := by
    rw [← (unknownIndex q).sum_comp
      (fun j => (generatedInt a u (equationIndex q e) (some j) : ℚ) * x j)]
    simp_rw [← Option.map_some, generatedInt_selected a u hv, augment, Matrix.of_apply,
      Option.elim'_some, mul_assoc, ← Finset.mul_sum]
    rfl
  have hrhs (e : Equation q) :
      (generatedInt a u (equationIndex q e) none : ℚ) = scale a e * encoderRhs u e :=
    generatedInt_selected a u hv e none
  constructor
  · intro h e
    have he := h (equationIndex q e)
    rw [hsum, hrhs] at he
    have hd : ((a e.1).den.number : ℚ) ≠ 0 := by exact_mod_cast hv e.1
    exact mul_left_cancel₀ (pow_ne_zero _ hd) he
  · intro h i
    obtain ⟨e, rfl⟩ := (equationIndex q).surjective i
    rw [hsum, hrhs, h e]

theorem generated_consistent {q : ℕ} (a : Fin q → Fraction) (u : Word q)
    (hv : ∀ t, (a t).valid) (hq : 2 ≤ q)
    (hi : Function.Injective (physicalLabels a)) (hn : ∀ t, physicalLabels a t ≠ 0) :
    ∃ x : Fin (unknownCount q) → ℚ, ∀ i,
      (∑ j, (generatedInt a u i (some j) : ℚ) * x j) = (generatedInt a u i none : ℚ) := by
  obtain ⟨x, hx⟩ := denseEncoder_consistent (physicalLabels a) u hq hi hn
  exact ⟨x, (generated_system_iff a u hv x).mpr
    ((encoderInt_system_iff (physicalLabels a) u _).mp
      ((denseEncoder_system_iff (physicalLabels a) u x).mp hx))⟩

theorem paired_of_generated_solutions {q : ℕ} (a : Fin q → Fraction) (hv : ∀ t, (a t).valid)
    (x : Word q → Fin (unknownCount q) → ℚ)
    (h : ∀ u i, (∑ j, (generatedInt a u i (some j) : ℚ) * x u j) =
      (generatedInt a u i none : ℚ)) :
    PairedCondition (physicalLabels a) (binaryEncoder q) (q-2)
      (fun u => solutionPolynomial u (decodeSolution (x u))) :=
  paired_of_encoderInt_solutions (physicalLabels a) (fun u => decodeSolution (x u))
    (fun u => (encoderInt_system_iff (physicalLabels a) u _).mpr
      ((generated_system_iff a u hv (x u)).mp (h u)))

end Reconstruction.BareissPaper
