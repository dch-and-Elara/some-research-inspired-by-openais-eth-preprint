import P5A11SharpFibres
import Mathlib.Data.Finset.Sort

/-! Explicit increasing ordinalization of the consecutive repeated
node blocks; the ordinal position really is the Newton column degree. -/
namespace Paper5
open scoped BigOperators Classical
variable {T : Type*} [Fintype T] [LinearOrder T]

omit [LinearOrder T] in
theorem node_order_card (k : T→ℕ) : Fintype.card (NodeOrder k)=∑ u,k u := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]

noncomputable def orderedNodeEquiv (k : T→ℕ) : Fin (∑u,k u) ≃ NodeOrder k :=
  letI : LinearOrder (NodeOrder k) := LinearOrder.lift' nodeKey nodeKey_injective
  (Fintype.orderIsoFinOfCardEq (NodeOrder k) (node_order_card k)).toEquiv

theorem orderedNodeEquiv_lt (k : T→ℕ) (i j : Fin (∑u,k u)) :
    nodeKey (orderedNodeEquiv k i)<nodeKey (orderedNodeEquiv k j) ↔ i<j := by
  letI : LinearOrder (NodeOrder k) := LinearOrder.lift' nodeKey nodeKey_injective
  let e := Fintype.orderIsoFinOfCardEq (NodeOrder k) (node_order_card k)
  change e i<e j ↔ i<j
  exact e.lt_iff_lt

theorem ordered_prefix_card (k : T→ℕ) (i : Fin (∑u,k u)) :
    (Finset.univ.filter (fun a : NodeOrder k=>nodeKey a<nodeKey (orderedNodeEquiv k i))).card=i.val := by
  let f := orderedNodeEquiv k
  have he : (Finset.Iio i).image f=
      Finset.univ.filter (fun a : NodeOrder k=>nodeKey a<nodeKey (f i)) := by
    ext a
    simp only [Finset.mem_image,Finset.mem_Iio,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨j,hj,rfl⟩
      exact (orderedNodeEquiv_lt k j i).mpr hj
    · intro h
      refine ⟨f.symm a,(orderedNodeEquiv_lt k (f.symm a) i).mp ?_,f.apply_symm_apply a⟩
      rwa [show orderedNodeEquiv k (f.symm a)=a from f.apply_symm_apply a]
  rw [←he,Finset.card_image_of_injective _ f.injective,Fin.card_Iio]

omit [Fintype T] in
theorem nodeKey_lt_cases {k : T→ℕ} (a b : NodeOrder k) :
    nodeKey a<nodeKey b ↔ a.1<b.1 ∨ (a.1=b.1 ∧ a.2.val<b.2.val) := by
  change Prod.Lex (· < ·) (· < ·) (a.1,a.2.val) (b.1,b.2.val) ↔ _
  exact Prod.lex_def

theorem same_node_prefix_card (k : T→ℕ) (x : NodeOrder k) :
    (Finset.univ.filter (fun a : NodeOrder k=>a.1=x.1 ∧ a.2.val<x.2.val)).card=x.2.val := by
  let f (i : Fin x.2.val) : NodeOrder k := ⟨x.1,⟨i.val,i.isLt.trans x.2.isLt⟩⟩
  have hi : Function.Injective f := by
    intro i j h
    exact Fin.ext (congrArg (fun a : NodeOrder k=>a.2.val) h)
  have h : (Finset.univ : Finset (Fin x.2.val)).image f =
      Finset.univ.filter (fun a : NodeOrder k=>a.1=x.1 ∧ a.2.val<x.2.val) := by
    ext a
    simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨rfl,i.isLt⟩
    · rcases a with ⟨u,i⟩
      rintro ⟨hu,hi'⟩
      change u=x.1 at hu
      subst u
      exact ⟨⟨i.val,hi'⟩,rfl⟩
  rw [←h,Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_fin]

theorem shape_node_prefix_card (k : T→ℕ) (x : NodeOrder k) :
    (Finset.univ.filter (fun a : NodeOrder k=>nodeKey a<nodeKey x)).card =
      (∑ u∈earlierNodes x.1,k u)+x.2.val := by
  let S := Finset.univ.filter (fun a : NodeOrder k=>a.1<x.1)
  let U := Finset.univ.filter (fun a : NodeOrder k=>a.1=x.1 ∧ a.2.val<x.2.val)
  have he : Finset.univ.filter (fun a : NodeOrder k=>nodeKey a<nodeKey x)=S∪U := by
    ext a
    simp only [S,U,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,nodeKey_lt_cases]
  have hd : Disjoint S U := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact ((Finset.mem_filter.mp ha).2.ne) ((Finset.mem_filter.mp hb).2.1)
  rw [he,Finset.card_union_of_disjoint hd]
  change (Finset.univ.filter (fun a : NodeOrder k=>a.1<x.1)).card+U.card=_
  exact congrArg₂ Nat.add (whole_slot_filter_by_node k (fun u=>u<x.1))
    (same_node_prefix_card k x)

theorem block_prefix_is_ordinal (k : T→ℕ) (i : Fin (∑u,k u)) :
    (∑ u∈earlierNodes (orderedNodeEquiv k i).1,k u)+(orderedNodeEquiv k i).2.val=i.val :=
  (shape_node_prefix_card k _).symm.trans (ordered_prefix_card k i)

#print axioms orderedNodeEquiv_lt
#print axioms ordered_prefix_card
#print axioms block_prefix_is_ordinal
end Paper5
