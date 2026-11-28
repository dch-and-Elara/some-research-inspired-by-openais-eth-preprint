import F5R61ForbiddenClassification
import F5R61ActualCycleLists

/-! The classified pairs are exactly the actually emitted list, before
and after filtering for one logical name. No new pair is inserted. -/
namespace F5R61
open F5R60
set_option autoImplicit false
set_option linter.unusedSimpArgs false
variable {V E T : Type}

theorem original_forward_pair_iff_mem
    (v : Listing V) (e : Listing E) (t : Listing T) (p q : PrivatePos V E T) :
    OriginalForwardPair p q ↔ (p,q) ∈ allForbidden v e t := by
  constructor
  · intro h
    cases h with
    | switch a =>
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨a,v.all a,rfl⟩))
    | edge a =>
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨a,e.all a,rfl⟩))
    | triple a =>
      exact List.mem_append_right _ (List.mem_map.mpr ⟨a,t.all a,rfl⟩)
  · intro h
    simp only [allForbidden,List.mem_append,switches,directedRequests,tripleRequests,List.mem_map] at h
    rcases h with (⟨a,_,h⟩ | ⟨a,_,h⟩) | ⟨a,_,h⟩
    · obtain ⟨l,r⟩ := Prod.mk.inj h
      exact l ▸ r ▸ OriginalForwardPair.switch a
    · obtain ⟨l,r⟩ := Prod.mk.inj h
      exact l ▸ r ▸ OriginalForwardPair.edge a
    · obtain ⟨l,r⟩ := Prod.mk.inj h
      exact l ▸ r ▸ OriginalForwardPair.triple a

theorem repeat_iff_actual_forbidden (G : RequestGraph V E T) (D : DistinctSourceEnds G)
    (v : Listing V) (e : Listing E) (t : Listing T) (p q : PrivatePos V E T) :
    RepeatInOriginalClause G p q ↔ (p,q) ∈ allForbidden v e t ∨ (q,p) ∈ allForbidden v e t :=
  (original_repeat_iff_pair_shapes G D p q).trans
    (or_congr (original_forward_pair_iff_mem v e t p q) (original_forward_pair_iff_mem v e t q p))

theorem repeat_iff_actual_forbidden_in_fibre [DecidableEq V] [DecidableEq T]
    (G : RequestGraph V E T) (D : DistinctSourceEnds G)
    (v : Listing V) (e : Listing E) (t : Listing T) (p q : PrivatePos V E T) (n : Logical V T) :
    RepeatInOriginalClause G p q ∧ nameOf G p=n ↔
      (p,q) ∈ pairsOf G v e t n ∨ (q,p) ∈ pairsOf G v e t n := by
  constructor
  · rintro ⟨same,atName⟩
    have atOther : nameOf G q=n := same.1.symm.trans atName
    rcases (repeat_iff_actual_forbidden G D v e t p q).1 same with left | right
    · exact Or.inl (List.mem_filter.mpr ⟨left,by simpa only [decide_eq_true_eq]⟩)
    · exact Or.inr (List.mem_filter.mpr ⟨right,by simpa only [decide_eq_true_eq]⟩)
  · rintro (left | right)
    · obtain ⟨h,hname⟩ := List.mem_filter.mp left
      exact ⟨(repeat_iff_actual_forbidden G D v e t p q).2 (Or.inl h),by simpa using hname⟩
    · obtain ⟨h,hname⟩ := List.mem_filter.mp right
      have same := (repeat_iff_actual_forbidden G D v e t p q).2 (Or.inr h)
      exact ⟨same,same.1.trans (by simpa using hname)⟩

#print axioms original_forward_pair_iff_mem
#print axioms repeat_iff_actual_forbidden
#print axioms repeat_iff_actual_forbidden_in_fibre
end F5R61
