import MainClonedCNF
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Tactic

/-! §8 triangle replacement of an actual finite cubic graph.  Stored
edges have a provisional orientation. The outgoing/incoming incidence
slots are distinguished and then assigned bijectively to the three
vertices of each triangle; the new exterior edges form a perfect
matching. -/
namespace Paper5.HybridClosure
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev TriVertex (V : Type*) := V × Fin 3

private def incidenceSigma (E : Finset (V×V)) :
    E×Bool ≃ (Σ v : V, MainClonedCNF.EndpointSlot E v) where
  toFun p :=
    match p.2 with
    | false => ⟨p.1.val.1,.inl ⟨p.1.val,Finset.mem_filter.mpr ⟨p.1.property,rfl⟩⟩⟩
    | true => ⟨p.1.val.2,.inr ⟨p.1.val,Finset.mem_filter.mpr ⟨p.1.property,rfl⟩⟩⟩
  invFun p :=
    match p.2 with
    | .inl e => (⟨e.val,(Finset.mem_filter.mp e.property).1⟩,false)
    | .inr e => (⟨e.val,(Finset.mem_filter.mp e.property).1⟩,true)
  left_inv := by
    rintro ⟨e,b⟩
    cases b <;> rfl
  right_inv := by
    rintro ⟨v,slot⟩
    rcases slot with ⟨e,he⟩|⟨e,he⟩
    · have hv : e.1=v := (Finset.mem_filter.mp he).2
      subst v
      rfl
    · have hv : e.2=v := (Finset.mem_filter.mp he).2
      subst v
      rfl

noncomputable def exteriorPort (E : Finset (V×V))
    (cubic : ∀ v, GraphCutMoments.degree E v=3) : E×Bool ≃ TriVertex V :=
  (incidenceSigma E).trans ((Equiv.sigmaCongrRight fun v => MainClonedCNF.edgeNumber E cubic v).trans
    (Equiv.sigmaEquivProd V (Fin 3)))

omit [Fintype V] in
theorem exteriorPort_left_base (E : Finset (V×V))
    (cubic : ∀ v, GraphCutMoments.degree E v=3) (e : E) :
    (exteriorPort E cubic (e,false)).1=e.val.1 := rfl

omit [Fintype V] in
theorem exteriorPort_right_base (E : Finset (V×V))
    (cubic : ∀ v, GraphCutMoments.degree E v=3) (e : E) :
    (exteriorPort E cubic (e,true)).1=e.val.2 := rfl

def innerEdge (p : TriVertex V) : TriVertex V×TriVertex V := (p,(p.1,p.2+1))

noncomputable def outerEdge (E : Finset (V×V))
    (cubic : ∀ v, GraphCutMoments.degree E v=3) (e : E) : TriVertex V×TriVertex V :=
  (exteriorPort E cubic (e,false),exteriorPort E cubic (e,true))

omit [Fintype V] [DecidableEq V] in
theorem innerEdge_injective : Function.Injective (@innerEdge V) :=
  fun _ _ h => congrArg Prod.fst h

omit [Fintype V] in
theorem outerEdge_injective (E : Finset (V×V)) (cubic : ∀ v, GraphCutMoments.degree E v=3) :
    Function.Injective (outerEdge E cubic) := by
  intro e f h
  exact congrArg Prod.fst ((exteriorPort E cubic).injective (congrArg Prod.fst h))

def innerEdges (V : Type*) [Fintype V] [DecidableEq V] : Finset (TriVertex V×TriVertex V) :=
  Finset.univ.image innerEdge

noncomputable def outerEdges (E : Finset (V×V))
    (cubic : ∀ v, GraphCutMoments.degree E v=3) : Finset (TriVertex V×TriVertex V) :=
  Finset.univ.image (outerEdge E cubic)

noncomputable def replacedEdges (E : Finset (V×V))
    (cubic : ∀ v, GraphCutMoments.degree E v=3) : Finset (TriVertex V×TriVertex V) :=
  innerEdges V ∪ outerEdges E cubic

theorem innerEdges_stay_in_triangle {e : TriVertex V×TriVertex V}
    (he : e∈innerEdges V) : e.1.1=e.2.1 := by
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp he
  rfl

omit [Fintype V] in
theorem outerEdges_join_distinct_triangles (E : Finset (V×V))
    (cubic : ∀ v, GraphCutMoments.degree E v=3) (loopless : ∀ v,(v,v)∉E)
    {e : TriVertex V×TriVertex V} (he : e∈outerEdges E cubic) : e.1.1≠e.2.1 := by
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp he
  change (exteriorPort E cubic (p,false)).1≠(exteriorPort E cubic (p,true)).1
  rw [exteriorPort_left_base,exteriorPort_right_base]
  intro h
  have ep : p.val=(p.val.1,p.val.1) := Prod.ext rfl h.symm
  exact loopless p.val.1 (ep ▸ p.property)

theorem triangle_split_disjoint (E : Finset (V×V)) (cubic : ∀ v, GraphCutMoments.degree E v=3)
    (loopless : ∀ v,(v,v)∉E) : Disjoint (innerEdges V) (outerEdges E cubic) :=
  Finset.disjoint_left.mpr fun _ h1 h2 =>
    outerEdges_join_distinct_triangles E cubic loopless h2 (innerEdges_stay_in_triangle h1)

omit [Fintype V] in
theorem disjoint_exterior_incidence (E : Finset (V×V))
    (cubic : ∀ v, GraphCutMoments.degree E v=3) :
    ∀ (v : TriVertex V), ∃! p : E×Bool, exteriorPort E cubic p=v := by
  intro v
  exact ⟨(exteriorPort E cubic).symm v,(exteriorPort E cubic).apply_symm_apply v,
    fun p hp => (exteriorPort E cubic).injective (hp.trans ((exteriorPort E cubic).apply_symm_apply v).symm)⟩

theorem triangle_inner_count : (innerEdges V).card = 3*Fintype.card V := by
  unfold innerEdges
  rw [Finset.card_image_of_injective _ innerEdge_injective,Finset.card_univ,Fintype.card_prod,Fintype.card_fin]
  omega

omit [Fintype V] in
theorem triangle_outer_count (E : Finset (V×V)) (cubic : ∀ v,GraphCutMoments.degree E v=3) :
    (outerEdges E cubic).card=E.card := by
  unfold outerEdges
  rw [Finset.card_image_of_injective _ (outerEdge_injective E cubic),Finset.card_univ,Fintype.card_coe]

theorem triangle_edge_count (E : Finset (V×V)) (cubic : ∀ v,GraphCutMoments.degree E v=3)
    (loopless : ∀ v,(v,v)∉E) :
    2*(replacedEdges E cubic).card = 3*Fintype.card (TriVertex V) := by
  unfold replacedEdges
  rw [Finset.card_union_of_disjoint (triangle_split_disjoint E cubic loopless),
    triangle_inner_count,triangle_outer_count,Fintype.card_prod,Fintype.card_fin]
  have h := GraphCutMoments.regular_edge_count E 3 cubic
  omega

#print axioms exteriorPort
#print axioms triangle_split_disjoint
#print axioms disjoint_exterior_incidence
#print axioms triangle_inner_count
#print axioms triangle_outer_count
#print axioms triangle_edge_count
end Paper5.HybridClosure
