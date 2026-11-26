import P5A11SharpDet

/-! Cardinal probes for true node/order slots, independent of the choice
of ordering used for precision priority. -/
namespace Paper5
open scoped BigOperators Classical

variable {T : Type*} [Fintype T] [DecidableEq T]

def nodeFiberEquiv (k : T→ℕ) (u : T) : {x : NodeOrder k // x.1=u} ≃ Fin (k u) where
  toFun x := Fin.cast (congrArg k x.property) x.val.2
  invFun i := ⟨⟨u,i⟩,rfl⟩
  left_inv := by
    rintro ⟨⟨v,i⟩,h⟩
    change v=u at h
    subst v
    rfl
  right_inv _ := rfl

theorem whole_node_fiber_card (k : T→ℕ) (u : T) :
    (Finset.univ.filter (fun x : NodeOrder k=>x.1=u)).card=k u := by
  rw [←Fintype.card_subtype,Fintype.card_congr (nodeFiberEquiv k u),Fintype.card_fin]

theorem selected_node_fiber_card_le (k : T→ℕ) (A : Finset (NodeOrder k)) (u : T) :
    (A.filter (fun x=>x.1=u)).card≤k u := by
  rw [←whole_node_fiber_card k u]
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))

theorem whole_slot_filter_by_node (k : T→ℕ) (p : T→Prop) [DecidablePred p] :
    (Finset.univ.filter (fun x : NodeOrder k=>p x.1)).card =
      ∑ u ∈ Finset.univ.filter p,k u := by
  have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset (NodeOrder k))
    (Finset.univ.filter p) (fun x=>x.1)
  simp_rw [whole_node_fiber_card] at h
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using h.symm

theorem selected_slot_filter_by_node (k : T→ℕ) (A : Finset (NodeOrder k))
    (p : T→Prop) [DecidablePred p] :
    (A.filter (fun x=>p x.1)).card =
      ∑ u ∈ Finset.univ.filter p,(A.filter (fun x=>x.1=u)).card := by
  have h := Finset.sum_card_fiberwise_eq_card_filter A (Finset.univ.filter p) (fun x=>x.1)
  simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using h.symm

#print axioms whole_node_fiber_card
#print axioms selected_node_fiber_card_le
#print axioms whole_slot_filter_by_node
#print axioms selected_slot_filter_by_node
end Paper5
