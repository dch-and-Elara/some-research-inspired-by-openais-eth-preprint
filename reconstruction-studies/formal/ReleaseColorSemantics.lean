import ColorAlphabetModel
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

open scoped BigOperators

namespace Reconstruction.ReleaseColor

noncomputable section

universe uI

variable {V F : Type*} {I : Type uI} [Fintype V] [Fintype I] [Field F]

/-- A row acts on the full physical input space by the ordinary dot product. -/
def rowForm (r : V → F) : (V → F) →ₗ[F] F :=
  ∑ v, r v • LinearMap.proj v

@[simp] theorem rowForm_apply (r z : V → F) : rowForm r z = ∑ v, r v * z v := by
  simp [rowForm, LinearMap.sum_apply, smul_eq_mul]

def observations (C : Matrix I V F) (S : Finset V) (z : V → F) :
    (I → F) × (S → F) :=
  (fun i => rowForm (C i) z, fun v => z v.val)

/-- Recoverability by an arbitrary decoder is precisely the common-kernel test. -/
theorem arbitraryDecoder_iff_kernel (C : Matrix I V F) (S : Finset V) (r : V → F) :
    (∃ D : ((I → F) × (S → F)) → F, ∀ z, D (observations C S z) = rowForm r z) ↔
    ∀ z : V → F, (∀ i, rowForm (C i) z = 0) → (∀ v ∈ S, z v = 0) →
      rowForm r z = 0 := by
  classical
  constructor
  · rintro ⟨D,hD⟩ z hz hs
    have he : observations C S z = observations C S 0 := by
      apply Prod.ext
      · funext i
        exact (hz i).trans (map_zero _).symm
      · funext v
        exact hs v.val v.property
    rw [← hD z, he, hD, map_zero]
  · intro hk
    let D (y : (I → F) × (S → F)) : F :=
      if h : ∃ z, observations C S z = y then rowForm r (Classical.choose h) else 0
    refine ⟨D, fun z => ?_⟩
    have he : ∃ w, observations C S w = observations C S z := ⟨z,rfl⟩
    change D (observations C S z) = _
    dsimp only [D]
    rw [dif_pos he]
    let w := Classical.choose he
    have hw := Classical.choose_spec he
    have hC (i : I) : rowForm (C i) (w-z) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact congrArg (fun y : (I → F) × (S → F) => y.1 i) hw
    have hS (v : V) (hv : v ∈ S) : (w-z) v = 0 := by
      change w v - z v = 0
      exact sub_eq_zero.mpr (congrArg (fun y : (I → F) × (S → F) => y.2 ⟨v,hv⟩) hw)
    have hr := hk (w-z) hC hS
    rwa [map_sub, sub_eq_zero] at hr

/-- The common-kernel criterion is equivalent to membership in the span of
the measurement rows together with the available coordinate functionals. -/
theorem kernel_iff_observation_span (C : Matrix I V F) (S : Finset V) (r : V → F) :
    (∀ z : V → F, (∀ i, rowForm (C i) z = 0) → (∀ v ∈ S, z v = 0) →
      rowForm r z = 0) ↔
    rowForm r ∈ Submodule.span F (Set.range (fun i => rowForm (C i))) ⊔
      Submodule.span F (Set.range (fun v : S => (LinearMap.proj v.val : (V → F) →ₗ[F] F))) := by
  classical
  let obs : I ⊕ S → (V → F) →ₗ[F] F :=
    Sum.elim (fun i => rowForm (C i)) (fun v : S => LinearMap.proj v.val)
  have he : Submodule.span F (Set.range obs) =
      Submodule.span F (Set.range (fun i => rowForm (C i))) ⊔
        Submodule.span F (Set.range (fun v : S => (LinearMap.proj v.val : (V → F) →ₗ[F] F))) := by
    rw [← Submodule.span_union]
    congr 1
    ext p
    constructor
    · rintro ⟨i,rfl⟩
      rcases i with i | v
      · exact Or.inl ⟨i,rfl⟩
      · exact Or.inr ⟨v,rfl⟩
    · rintro (⟨i,rfl⟩ | ⟨v,rfl⟩)
      · exact ⟨Sum.inl i,rfl⟩
      · exact ⟨Sum.inr v,rfl⟩
  rw [← he]
  constructor
  · intro hk
    apply mem_span_of_iInf_ker_le_ker
    intro z hz
    have hm := ((Submodule.mem_iInf _).mp hz)
    exact hk z (fun i => hm (Sum.inl i)) (fun v hv => hm (Sum.inr ⟨v,hv⟩))
  · intro hr z hC hS
    obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun F).mp hr
    have hh := LinearMap.congr_fun hc z
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at hh
    rw [← hh]
    apply Finset.sum_eq_zero
    intro i _
    rcases i with j | v
    · exact mul_eq_zero_of_right _ (hC j)
    · exact mul_eq_zero_of_right _ (hS v.val v.property)

omit [Fintype I] in
/-- A finite broadcast matrix can be shortened to exactly its rank by keeping
an independent subfamily of the original rows, preserving their span. -/
theorem independent_broadcast_rows [Finite I] (C : Matrix I V F) :
    ∃ (J : Type uI) (hJ : Fintype J) (e : J ↪ I),
      @Fintype.card J hJ = C.rank ∧
        Submodule.span F (Set.range (C.row ∘ e)) = Submodule.span F (Set.range C.row) := by
  classical
  obtain ⟨J,e,he,hs,hl⟩ := exists_linearIndependent' F C.row
  letI : Finite J := Finite.of_injective e he
  letI : Fintype J := Fintype.ofFinite J
  let A := C.submatrix e id
  have hlin : LinearIndependent F A.row := hl
  have hcard := hlin.rank_matrix
  have hrank : A.rank = C.rank := by
    rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row]
    change Module.finrank F (Submodule.span F (Set.range (C.row ∘ e))) = _
    rw [hs]
  exact ⟨J,inferInstance,⟨e,he⟩,hcard.symm.trans hrank,hs⟩

end
end Reconstruction.ReleaseColor
