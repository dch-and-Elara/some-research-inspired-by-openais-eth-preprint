import ReleaseColor
import ColorAlphabetUpper

open scoped BigOperators Polynomial
open Reconstruction.ColorAlphabet

namespace Reconstruction.ReleaseColor

noncomputable section

variable {n : ℕ} {even : Bool} {F : Type*} [Field F]

private abbrev Pair (n : ℕ) (even : Bool) := Letters n even × Letters n even

/-- The concrete round-robin rows are a basis, as required in the application
of the total-color lemma. -/
def roundBasis (θ : F) (hθ : θ ≠ 1) :
    Module.Basis (Pair n even) F (Pair n even → F) := by
  classical
  let S := Submodule.span F (Set.range (@localEntry n even F _ θ))
  have hc (u : Pair n even) : coordinateRow (F := F) u ∈ S := by
    obtain ⟨c, hc⟩ := local_expands θ hθ u
    have he : (∑ k, c k • localEntry θ k) = coordinateRow (F := F) u := by
      funext v
      simpa [Finset.sum_apply, smul_eq_mul, coordinateRow] using hc v
    rw [← he]
    exact S.sum_mem (fun k _ =>
      S.smul_mem _ (Submodule.subset_span ⟨k, rfl⟩))
  have htop : S = ⊤ := by
    apply le_antisymm le_top
    intro x _
    have he : (∑ u : Pair n even, x u • coordinateRow (F := F) u) = x := by
      funext v
      simp [Finset.sum_apply, coordinateRow, smul_eq_mul, mul_ite]
    rw [← he]
    exact S.sum_mem (fun u _ => S.smul_mem _ (hc u))
  have hind : LinearIndependent F (@localEntry n even F _ θ) := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    change _ = Module.finrank F S
    rw [htop, finrank_top, Module.finrank_pi]
  exact Module.Basis.mk hind (by change ⊤ ≤ S; rw [htop])

@[simp] theorem roundBasis_apply (θ : F) (hθ : θ ≠ 1) (k : Pair n even) :
    roundBasis θ hθ k = localEntry θ k := by
  unfold roundBasis
  exact Module.Basis.mk_apply _ _ _

/-- Exact rank of the displayed round-robin code, in both alphabet parities. -/
theorem roundEncoder_exact_rank (θ : F) (hθ : θ ≠ 1) (n : ℕ) (even : Bool) (q : ℕ) :
    (roundEncoder F θ n even q).rank =
      (2*n+1) * ((alphabetSize n even ^ (2*q) - (n+1)^q) / (2*(2*n+1)+1)) := by
  have hr := tensor_basis_rank_card (roundBasis (n := n) (even := even) θ hθ)
    localColor (InInterval 1) q
  have he : (fun k => roundBasis (n := n) (even := even) θ hθ k) = fun k => localEntry θ k :=
    funext (roundBasis_apply θ hθ)
  rw [he] at hr
  exact hr.trans (roundEncoder_rows n even q)

end
end Reconstruction.ReleaseColor
