import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-! No two incidences occupy the same physical (copy, cell) slot.
Disjoint variable supports give the actual orthonormal test columns used
by F.A1, including variable-dependent incidence multiplicities. -/
namespace P5MainIterator
open scoped BigOperators RealInnerProductSpace Classical

variable {E V S : Type*} [Fintype E] [Fintype V] [Fintype S]

structure Placement (E V S : Type*) where
  owner : E → V
  slot : E ↪ S
  occurs : Function.Surjective owner

noncomputable def incidences (L : Placement E V S) (v : V) : Finset E :=
  Finset.univ.filter (fun e => L.owner e=v)

noncomputable def filled (L : Placement E V S) (v : V) : Finset S :=
  (incidences L v).image L.slot

omit [Fintype V] [Fintype S] in
theorem filled_card (L : Placement E V S) (v : V) :
    (filled L v).card = (incidences L v).card :=
  Finset.card_image_of_injective _ L.slot.injective

omit [Fintype V] [Fintype S] in
theorem filled_pos (L : Placement E V S) (v : V) : 0 < (filled L v).card := by
  rw [filled_card,Finset.card_pos]
  obtain ⟨e,he⟩ := L.occurs v
  exact ⟨e,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩⟩

omit [Fintype V] [Fintype S] in
theorem distinct_filled (L : Placement E V S) (v w : V) (hn : v≠w) :
    Disjoint (filled L v) (filled L w) := by
  rw [Finset.disjoint_left]
  intro s hv hw
  obtain ⟨e,he,hs⟩ := Finset.mem_image.mp hv
  obtain ⟨f,hf,ht⟩ := Finset.mem_image.mp hw
  have heq : e=f := L.slot.injective (hs.trans ht.symm)
  have he₁ := (Finset.mem_filter.mp he).2
  have hf₁ := (Finset.mem_filter.mp hf).2
  exact hn (he₁.symm.trans (heq ▸ hf₁))

noncomputable def columnScale (L : Placement E V S) (v : V) : ℝ :=
  (Real.sqrt ((filled L v).card : ℝ))⁻¹

omit [Fintype V] [Fintype S] in
theorem columnScale_square (L : Placement E V S) (v : V) :
    (columnScale L v)^2 = (((filled L v).card : ℝ)⁻¹) := by
  unfold columnScale
  rw [inv_pow,Real.sq_sqrt (by positivity)]

noncomputable def occupiedColumn (L : Placement E V S) (v : V) : EuclideanSpace ℝ S :=
  WithLp.toLp 2 (fun s => if s ∈ filled L v then columnScale L v else 0)

omit [Fintype V] in
theorem occupied_orthonormal (L : Placement E V S) : Orthonormal ℝ (occupiedColumn L) := by
  apply (orthonormal_iff_ite).2
  intro v w
  rw [EuclideanSpace.inner_eq_star_dotProduct,dotProduct]
  by_cases h : v=w
  · subst w
    rw [if_pos rfl]
    calc
      _ = ∑ s ∈ filled L v, (WithLp.ofLp (occupiedColumn L v) s) *
          (star (WithLp.ofLp (occupiedColumn L v)) s) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro s _ hs
        simp [occupiedColumn,hs]
      _ = ∑ s ∈ filled L v, (columnScale L v)^2 := by
        apply Finset.sum_congr rfl
        intro s hs
        simp [occupiedColumn,hs,pow_two]
      _ = (↑(filled L v).card:ℝ) * (columnScale L v)^2 := by simp
      _ = _ := by
        rw [columnScale_square]
        apply mul_inv_cancel₀
        exact_mod_cast (filled_pos L v).ne'
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro s _
    by_cases hv : s ∈ filled L v
    · have hw : s ∉ filled L w := fun hw => (Finset.disjoint_left.mp (distinct_filled L v w h)) hv hw
      simp [occupiedColumn,hw]
    · simp [occupiedColumn,hv]

/-- Squaring a sum supported at at most one slot creates no cross terms. -/
theorem sum_sq_when_unique {I : Type*} (s : Finset I) (f : I → ℝ)
    (h : ∀ i ∈ s, ∀ j ∈ s, f i≠0 → f j≠0 → i=j) :
    (∑ i ∈ s, f i)^2 = ∑ i ∈ s, (f i)^2 := by
  by_cases he : ∃ i ∈ s, f i≠0
  · obtain ⟨i,hi,hn⟩ := he
    have hz (j : I) (hj : j∈s) (hne : j≠i) : f j=0 :=
      by_contra fun h₁ => hne (h j hj i hi h₁ hn)
    rw [Finset.sum_eq_single i (fun j hj hn => hz j hj hn) (fun H => (H hi).elim)]
    rw [Finset.sum_eq_single i (fun j hj hn => by simp [hz j hj hn]) (fun H => (H hi).elim)]
  · have hz : ∀ i∈s, f i=0 := by
      intro i hi
      by_contra! hn
      exact he ⟨i,hi,hn⟩
    rw [Finset.sum_eq_zero hz]
    simp only [zero_pow (by decide : (2:ℕ)≠0)]
    symm
    exact Finset.sum_eq_zero (fun i hi => by simp [hz i hi])

#print axioms filled_card
#print axioms distinct_filled
#print axioms columnScale_square
#print axioms occupied_orthonormal
#print axioms sum_sq_when_unique
end P5MainIterator
