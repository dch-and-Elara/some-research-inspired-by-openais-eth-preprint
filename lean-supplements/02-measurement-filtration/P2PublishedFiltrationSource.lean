import P2PublishedFiltrationEq9

/-! Eq. (9) in the original incidence indexing: a node subset T and
a selected physical variable subset V0 with their full-row, clipped-column
measurement blocks. No alternate rank or replaced layout appears. -/
namespace Reconstruction.LayoutMismatch.PublishedFiltration
open Polynomial
open LayoutBudget (GroupFiber measurementRank restrictGroupMatrix)
open scoped BigOperators Polynomial
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
noncomputable section

variable {I V G Factor : Type*} [DecidableEq V] [DecidableEq I] [Fintype G] [DecidableEq G]
variable {Rows : I → G → Type*} [∀ t g, Fintype (Rows t g)]

theorem equation_nine_actual_incidence_axes (V₀ : Finset V) (T : Finset I) (j : ℕ)
    (node : I → ℚ) (a : I → V → G) (b : I → Factor → G) (chosen : V₀ → Factor)
    (C : ∀ t g, Matrix (Rows t g) (GroupFiber (a t) g) ℚ)
    (hT : T.Nonempty) :
    let src (t : T) (v : V₀) := a t.val v.val
    let tgt (t : T) (v : V₀) := b t.val (chosen v)
    let clipped (t : T) (g : G) : Matrix (Rows t.val g) (GroupFiber (src t) g) ℚ :=
      restrictGroupMatrix (Subtype.val : V₀ → V) (a t.val) g (C t.val g)
    Module.finrank ℚ (H (V:=V₀) (fun t : T => node t.val) j) -
        Module.finrank ℚ (FiltrationKernel (fun t : T => node t.val) src tgt clipped j) ≤
      (2^T.card / 2)*(∑ t : T, measurementRank (Subtype.val : V₀ → V) (a t.val) (C t.val)) := by
  dsimp only
  let src (t : T) (v : V₀) := a t.val v.val
  let tgt (t : T) (v : V₀) := b t.val (chosen v)
  let clipped (t : T) (g : G) : Matrix (Rows t.val g) (GroupFiber (src t) g) ℚ :=
    restrictGroupMatrix (Subtype.val : V₀ → V) (a t.val) g (C t.val g)
  have hk : 0 < Fintype.card T := by
    rw [Fintype.card_coe]
    exact Finset.card_pos.mpr hT
  simpa only [Fintype.card_coe, measurementRank, clipped] using
    equation_nine (fun t : T => node t.val) src tgt clipped j hk

#print axioms equation_nine_actual_incidence_axes
end
end Reconstruction.LayoutMismatch.PublishedFiltration

