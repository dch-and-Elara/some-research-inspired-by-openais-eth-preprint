import AffineEdgeModel
import Mathlib.LinearAlgebra.Matrix.Rank

open scoped BigOperators Polynomial

namespace AffineEdge.Orbit

noncomputable section

variable {q : ℕ} {A F I : Type*} [LinearOrder A] [Fintype A] [Field F]

abbrev Key (q : ℕ) (A : Type*) := Fin q → A × A

def key (w : PairWord q A) : Key q A :=
  fun i => (min (w.1 i) (w.2 i), max (w.1 i) (w.2 i))

def swap (w : PairWord q A) : PairWord q A := w.swap

omit [LinearOrder A] [Fintype A] in
@[simp] theorem swap_swap (w : PairWord q A) : swap (swap w) = w := rfl

omit [Fintype A] in
@[simp] theorem key_swap (w : PairWord q A) : key (swap w) = key w := by
  funext i
  simp [key, swap, min_comm, max_comm]

omit [Fintype A] in
theorem key_active (w : PairWord q A) (t : Fin q) :
    (key w t).1 ≠ (key w t).2 ↔ w.1 t ≠ w.2 t := by
  rcases le_total (w.1 t) (w.2 t) with h | h
  · simp [key, min_eq_left h, max_eq_right h]
  · simp [key, min_eq_right h, max_eq_left h, ne_comm]

def project (o : Key q A) : (PairWord q A → F) →ₗ[F] (PairWord q A → F) where
  toFun z v := if key v = o then z v else 0
  map_add' x y := by
    funext v
    by_cases h : key v = o <;> simp [h]
  map_smul' c x := by
    funext v
    by_cases h : key v = o <;> simp [h]

def rowSpan (C : Matrix I (PairWord q A) F) : Submodule F (PairWord q A → F) :=
  Submodule.span F (Set.range C)

/-- Stability under every physical orbit projection. This is equivalent to
the row space being a direct sum of subspaces supported on the swap orbits. -/
def Orbitwise (C : Matrix I (PairWord q A) F) : Prop :=
  ∀ o z, z ∈ rowSpan C → project o z ∈ rowSpan C

theorem orbitwise_iff_supported_sum (C : Matrix I (PairWord q A) F) :
    Orbitwise C ↔
      rowSpan C = ⨆ o : Key q A, rowSpan C ⊓ LinearMap.range (project o) := by
  constructor
  · intro h
    apply le_antisymm _ (iSup_le fun _ => inf_le_left)
    intro z hz
    have he : (∑ o : Key q A, project o z) = z := by
      funext v
      simp [project, Finset.sum_apply, Finset.sum_ite_eq]
    rw [← he]
    apply Submodule.sum_mem
    intro o _
    exact Submodule.mem_iSup_of_mem o ⟨h o z hz, ⟨z,rfl⟩⟩
  · intro h o z hz
    have he (p : Key q A) (x : PairWord q A → F) :
        project o (project p x) = if p = o then project p x else 0 := by
      funext v
      by_cases hp : p = o
      · subst p
        by_cases hv : key v = o <;> simp [project, hv]
      · by_cases hv : key v = o <;> simp [project, hp, hv, Ne.symm hp]
    have hle (p : Key q A) :
        rowSpan C ⊓ LinearMap.range (project p) ≤ Submodule.comap (project o) (rowSpan C) := by
      rintro z ⟨hz, x, rfl⟩
      change project o (project p x) ∈ rowSpan C
      rw [he]
      split
      · exact hz
      · exact Submodule.zero_mem _
    apply (iSup_le hle)
    rwa [← h]

omit [Fintype A] in
theorem orbitwise_of_supported_rows {C : Matrix I (PairWord q A) F}
    (h : ∀ j, ∃ o : Key q A, ∀ v, key v ≠ o → C j v = 0) : Orbitwise C := by
  intro o x hx
  suffices hle : rowSpan C ≤ Submodule.comap (project o) (rowSpan C) by exact hle hx
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  obtain ⟨p,hp⟩ := h j
  change project o (C j) ∈ rowSpan C
  by_cases ho : p = o
  · have he : project o (C j) = C j := by
      funext v
      by_cases hv : key v = o
      · simp [project, hv]
      · simp [project, hv, hp v (ho ▸ hv)]
    rw [he]
    exact Submodule.subset_span ⟨j,rfl⟩
  · have he : project o (C j) = 0 := by
      funext v
      by_cases hv : key v = o
      · simp [project, hv, hp v (hv ▸ Ne.symm ho)]
      · simp [project, hv]
    rw [he]
    exact Submodule.zero_mem _

theorem kernel_project {C : Matrix I (PairWord q A) F} (hC : Orbitwise C)
    (z : PairWord q A → F) (hz : ∀ j, ∑ v, C j v * z v = 0)
    (o : Key q A) (j : I) : (∑ v, C j v * project o z v) = 0 := by
  let L : (PairWord q A → F) →ₗ[F] F :=
    ∑ v, z v • LinearMap.proj v
  have hle : rowSpan C ≤ LinearMap.ker L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    simpa [L, LinearMap.sum_apply, smul_eq_mul, mul_comm] using hz i
  have h := hle (hC o (C j) (Submodule.subset_span ⟨j,rfl⟩))
  change L (project o (C j)) = 0 at h
  simpa [L, LinearMap.sum_apply, smul_eq_mul, project, mul_ite, mul_comm] using h

omit [LinearOrder A] in
theorem rank_le_of_independent_columns [Fintype I] {J : Type*} [Fintype J]
    (C : Matrix I (PairWord q A) F) (w : J → PairWord q A)
    (h : LinearIndependent F (C.col ∘ w)) : Fintype.card J ≤ C.rank := by
  rw [← finrank_span_eq_card h, Matrix.rank_eq_finrank_span_cols]
  apply Submodule.finrank_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨j,rfl⟩
  exact Submodule.subset_span ⟨w j,rfl⟩

theorem independent_physical_columns {J : Type*} [Fintype J]
    (C : Matrix I (PairWord q A) F) (w : J → PairWord q A) (hw : Function.Injective w)
    (h : ∀ z : PairWord q A → F, (∀ j, ∑ v, C j v * z v = 0) →
      (∀ v, v ∉ Set.range w → z v = 0) → ∀ j, z (w j) = 0) :
    LinearIndependent F (C.col ∘ w) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  let z (v : PairWord q A) := ∑ i, if w i = v then c i else 0
  have hker (i : I) : (∑ v, C i v * z v) = 0 := by
    simp only [z, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have he := congrFun hc i
    simpa [Matrix.col, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using he
  have hs (v : PairWord q A) (hv : v ∉ Set.range w) : z v = 0 := by
    have hn (i : J) : w i ≠ v := fun he => hv ⟨i,he⟩
    simp [z, hn]
  have hj := h z hker hs j
  change (∑ i, if w i = w j then c i else 0) = 0 at hj
  simpa only [hw.eq_iff, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hj

end
end AffineEdge.Orbit
