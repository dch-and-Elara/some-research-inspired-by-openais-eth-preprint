import P5HybridClosureTriangle

namespace Paper5.HybridClosure
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Count any additive vertex weight on the two ends of exterior edges.
    Each replacement vertex occurs just once in this sum. -/
theorem outer_weight_sum (E : Finset (V×V)) (cubic : ∀ v,GraphCutMoments.degree E v=3)
    {R : Type*} [AddCommMonoid R] (f : TriVertex V→R) :
    ∑ e ∈ outerEdges E cubic,(f e.1+f e.2) = ∑ z,f z := by
  classical
  unfold outerEdges
  rw [Finset.sum_image (fun _ _ _ _ h => outerEdge_injective E cubic h)]
  change (∑ e : E, (f (exteriorPort E cubic (e,false))+f (exteriorPort E cubic (e,true))))=_
  calc
    _ = ∑ p : E×Bool, f (exteriorPort E cubic p) := by
      rw [Fintype.sum_prod_type]
      simp [add_comm]
    _ = _ := Fintype.sum_equiv (exteriorPort E cubic) _ _ (fun _ => rfl)

/-- Every replacement vertex occurs twice among the ends of the edges
    in its own triangle. -/
theorem inner_weight_sum {R : Type*} [AddCommMonoid R] (f : TriVertex V→R) :
    ∑ e ∈ innerEdges V, (f e.1+f e.2) = (∑ z, f z)+(∑ z, f z) := by
  classical
  unfold innerEdges
  rw [Finset.sum_image (fun _ _ _ _ h => innerEdge_injective h),Finset.sum_add_distrib]
  change (∑ z : TriVertex V, f z)+(∑ z : TriVertex V,f (z.1,z.2+1))=_
  congr 1
  exact Fintype.sum_equiv (Equiv.prodCongr (Equiv.refl V) (Equiv.addRight (1:Fin 3))) _ _
    (fun _ => rfl)

theorem replaced_cubic (E : Finset (V×V)) (cubic : ∀ v,GraphCutMoments.degree E v=3)
    (loopless : ∀ v,(v,v)∉E) : ∀ z,GraphCutMoments.degree (replacedEdges E cubic) z=3 := by
  classical
  intro z
  let f : TriVertex V→ℕ := fun v => if v=z then 1 else 0
  have hs : (∑ v, f v)=1 := by simp [f]
  have h := GraphCutMoments.weighted_incidence (replacedEdges E cubic) f
  calc
    _ = ∑ v, (GraphCutMoments.degree (replacedEdges E cubic) v : ℕ) * f v := by simp [f]
    _ = ∑ e ∈ replacedEdges E cubic,(f e.1+f e.2) := h.symm
    _ = _ := by
      rw [replacedEdges,Finset.sum_union (triangle_split_disjoint E cubic loopless),
        inner_weight_sum,outer_weight_sum,hs]

theorem replaced_loopless (E : Finset (V×V)) (cubic : ∀ v,GraphCutMoments.degree E v=3)
    (loopless : ∀ v,(v,v)∉E) : ∀ z,(z,z)∉replacedEdges E cubic := by
  intro z hz
  rcases Finset.mem_union.mp hz with hi|ho
  · obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hi
    have h₁ := congrArg Prod.fst hp
    have h₂ := congrArg Prod.snd hp
    change p=z at h₁
    subst p
    have hbad : z.2+1=z.2 := congrArg Prod.snd h₂
    have hstep : ∀ i : Fin 3, i+1≠i := by decide
    exact hstep z.2 hbad
  · exact outerEdges_join_distinct_triangles E cubic loopless ho rfl

theorem replaced_no_reversed (E : Finset (V×V)) (cubic : ∀ v,GraphCutMoments.degree E v=3)
    (loopless : ∀ v,(v,v)∉E) {u v : TriVertex V}
    (huv : (u,v)∈replacedEdges E cubic) : (v,u)∉replacedEdges E cubic := by
  intro hvu
  rcases Finset.mem_union.mp huv with hii|hio <;> rcases Finset.mem_union.mp hvu with hoi|hoo
  · obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hii
    obtain ⟨q,_,hq⟩ := Finset.mem_image.mp hoi
    have hp1 : p=u := congrArg Prod.fst hp
    have hq1 : q=v := congrArg Prod.fst hq
    subst p
    subst q
    have hp2 : u.2+1=v.2 := congrArg (Prod.snd ∘ Prod.snd) hp
    have hq2 : v.2+1=u.2 := congrArg (Prod.snd ∘ Prod.snd) hq
    rw [←hp2] at hq2
    have hstep : ∀ i : Fin 3, i+1+1≠i := by decide
    exact hstep u.2 hq2
  · exact outerEdges_join_distinct_triangles E cubic loopless hoo (innerEdges_stay_in_triangle hii).symm
  · exact outerEdges_join_distinct_triangles E cubic loopless hio (innerEdges_stay_in_triangle hoi).symm
  · obtain ⟨e,_,he⟩ := Finset.mem_image.mp hio
    obtain ⟨f,_,hf⟩ := Finset.mem_image.mp hoo
    have h₁ : exteriorPort E cubic (e,false)=u := congrArg Prod.fst he
    have h₂ : exteriorPort E cubic (f,true)=u := congrArg Prod.snd hf
    have hbad := (exteriorPort E cubic).injective (h₁.trans h₂.symm)
    have hft : false=true := congrArg Prod.snd hbad
    cases hft

#print axioms outer_weight_sum
#print axioms inner_weight_sum
#print axioms replaced_cubic
#print axioms replaced_loopless
#print axioms replaced_no_reversed
end Paper5.HybridClosure