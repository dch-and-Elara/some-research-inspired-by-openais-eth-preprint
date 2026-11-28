import P5OuterCenterGraph
import P5HybridClosureProduct

set_option warningAsError true
namespace Paper5.OuterCenters.Factors
open scoped BigOperators Classical
open Paper5.HybridClosure

variable {W : Type} [DecidableEq W]

omit [DecidableEq W] in
theorem factor_all_one (J : Finset (W×W)) :
    (∏ e ∈ J, edgeOr (fun _ => true) e) = 1 := by
  rw [edge_product_is_indicator]
  have h : PinnedCNF.AllEdges J (fun _ => true) := fun _ _ => Or.inl rfl
  exact if_pos h

theorem factor_zero_when_flipped_edge (J : Finset (W×W)) (x y : W)
    (edge : (x,y)∈J ∨ (y,x)∈J) :
    (∏ e ∈ J, edgeOr (signsWithTwoZero x y) e) = 0 := by
  rw [edge_product_is_indicator]
  apply if_neg
  intro h
  rcases edge with e|e
  · simpa [signsWithTwoZero] using h (x,y) e
  · simpa [signsWithTwoZero] using h (y,x) e

theorem factor_one_when_no_flipped_edge (J : Finset (W×W)) (x y : W)
    (avoid : ∀ e ∈ J, ¬ ((e.1=x ∨ e.1=y) ∧ (e.2=x ∨ e.2=y))) :
    (∏ e ∈ J, edgeOr (signsWithTwoZero x y) e) = 1 := by
  rw [edge_product_is_indicator]
  apply if_pos
  intro e he
  have h := avoid e he
  push_neg at h
  simp only [signsWithTwoZero, decide_eq_true_eq]
  by_cases hh : e.1 = x ∨ e.1 = y
  · exact Or.inr (h hh)
  · exact Or.inl (not_or.mp hh)

variable {V : Type} [Fintype V] [DecidableEq V]
variable (E : Finset (V×V)) (c : ∀ v,GraphCutMoments.degree E v=3)
variable (loopless : ∀ v,(v,v)∉E)

def innerMate (V : Type) : TriVertex V ≃ TriVertex V :=
  (Equiv.refl V).prodCongr (Equiv.addRight (1 : Fin 3))

theorem innerMate_edge (v : TriVertex V) : (v,innerMate V v) ∈ innerEdges V := by
  exact Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩

omit [Fintype V] in
theorem outerMate_outer (v : TriVertex V) :
    (v,exteriorMate E c v) ∈ outerEdges E c ∨
    (exteriorMate E c v,v) ∈ outerEdges E c := by
  classical
  obtain ⟨⟨e,b⟩,rfl⟩ := (exteriorPort E c).surjective v
  cases b
  · left
    exact Finset.mem_image.mpr ⟨e,Finset.mem_univ _,by
      simp [exteriorMate,outerEdge]
      rfl⟩
  · right
    exact Finset.mem_image.mpr ⟨e,Finset.mem_univ _,by
      simp [exteriorMate,outerEdge]
      rfl⟩

theorem innerEdges_distinct {e : TriVertex V×TriVertex V} (he : e∈innerEdges V) : e.1≠e.2 := by
  obtain ⟨v,_,rfl⟩ := Finset.mem_image.mp he
  intro h
  have hn : ∀ k : Fin 3, k≠k+1 := by decide
  exact hn v.2 (congrArg Prod.snd h)

include loopless in
theorem exterior_flip_isolates_exterior_factor (x : TriVertex V) :
    let τ := signsWithTwoZero x (exteriorMate E c x)
    (∏ e ∈ innerEdges V, edgeOr τ e) = 1 ∧ (∏ e ∈ outerEdges E c, edgeOr τ e) = 0 := by
  let y := exteriorMate E c x
  have houter : (x,y) ∈ outerEdges E c ∨ (y,x) ∈ outerEdges E c := outerMate_outer E c x
  have hxy : x.1 ≠ y.1 := by
    rcases houter with h|h
    · exact outerEdges_join_distinct_triangles E c loopless h
    · exact (outerEdges_join_distinct_triangles E c loopless h).symm
  refine ⟨factor_one_when_no_flipped_edge _ x y ?_,factor_zero_when_flipped_edge _ x y houter⟩
  intro e he ⟨h₁,h₂⟩
  have heq := innerEdges_stay_in_triangle he
  have hne := innerEdges_distinct he
  rcases h₁ with h₁|h₁ <;> rcases h₂ with h₂|h₂
  · exact hne (h₁.trans h₂.symm)
  · exact hxy (by simpa [h₁,h₂] using heq)
  · exact hxy (by simpa [h₁,h₂] using heq.symm)
  · exact hne (h₁.trans h₂.symm)

include loopless in
theorem triangle_flip_isolates_triangle_factor (x : TriVertex V) :
    let τ := signsWithTwoZero x (innerMate V x)
    (∏ e ∈ innerEdges V, edgeOr τ e) = 0 ∧ (∏ e ∈ outerEdges E c, edgeOr τ e) = 1 := by
  let y := innerMate V x
  refine ⟨factor_zero_when_flipped_edge _ x y (Or.inl (innerMate_edge x)),
    factor_one_when_no_flipped_edge _ x y ?_⟩
  intro e he ⟨h₁,h₂⟩
  have hne := outerEdges_join_distinct_triangles E c loopless he
  have heq : x.1 = y.1 := rfl
  rcases h₁ with h₁|h₁ <;> rcases h₂ with h₂|h₂ <;>
    exact hne (by simp [h₁,h₂,heq])

/-- This permutation may be substituted for exteriorMate in either
printed-root fiber theorem, with the same real packet layout. -/
theorem innerMate_exact_graph (x : TriVertex V) :
    (x,innerMate V x) ∈ replacedEdges E c ∨
      (innerMate V x,x) ∈ replacedEdges E c := by
  exact Or.inl (Finset.mem_union_left _ (innerMate_edge x))

#print axioms innerMate_exact_graph
#print axioms factor_all_one
#print axioms exterior_flip_isolates_exterior_factor
#print axioms triangle_flip_isolates_triangle_factor
end Paper5.OuterCenters.Factors




