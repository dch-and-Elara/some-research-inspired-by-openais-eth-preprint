import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Tactic.Abel

/-!
If one codeword realizes the projected inputs of every party, and the
party labels come from a submodule disjoint from the sum of the projection
kernels, then the labels agree. This is the restriction step in Section 1
of terminal_and_native.md. It is independent of alphabet and field size.
-/

namespace ProjectionDiagonal

variable {R E I : Type*} [Ring R] [AddCommGroup E] [Module R E]
variable {Y : I → Type*} [∀ i, AddCommGroup (Y i)] [∀ i, Module R (Y i)]

theorem realizable_iff_agree
    (first : I) (project : (i : I) → E →ₗ[R] Y i)
    (K W : Submodule R E) (hsep : Disjoint W K)
    (hk : ∀ i, LinearMap.ker (project i) ≤ K) (labels : I → W) :
    (∃ c : E, ∀ i, project i c = project i (labels i : E)) ↔
      ∀ i, labels i = labels first := by
  constructor
  · rintro ⟨c, hc⟩
    have hdiff (i : I) : c - (labels i : E) ∈ K := by
      apply hk i
      rw [LinearMap.mem_ker, map_sub, hc i, sub_self]
    intro i
    have hK : (labels i : E) - (labels first : E) ∈ K := by
      have h := K.sub_mem (hdiff first) (hdiff i)
      convert h using 1
      abel
    have hW : (labels i : E) - (labels first : E) ∈ W :=
      W.sub_mem (labels i).property (labels first).property
    apply Subtype.ext
    exact sub_eq_zero.mp ((Submodule.disjoint_def.mp hsep) _ hW hK)
  · intro hagree
    refine ⟨labels first, ?_⟩
    intro i
    rw [hagree i]

#print axioms realizable_iff_agree

end ProjectionDiagonal
