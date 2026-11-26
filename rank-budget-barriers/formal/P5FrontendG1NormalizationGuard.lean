import P5FrontendG1NormalizationRaw

/-! Literal source guard, with all original clause indices kept:
(z_v), (¬z_v ∨ L_v(x_v)), and (x_u ∨ x_v). -/
namespace Paper5.FrontendG1.Normalization
variable {V : Type*} [DecidableEq V]

def guardSet (E : Finset (V×V)) (sgn : V→Bool) (i : GuardIndex E) :
    ClauseSet (GuardVar V) := (guardedClause E sgn i).toFinset

@[simp] theorem guardSet_unit (E : Finset (V×V)) (sgn : V→Bool) (v : V) :
    guardSet E sgn (.inl v) = {(.inr v,true)} := by simp [guardSet,guardedClause]

@[simp] theorem guardSet_lock (E : Finset (V×V)) (sgn : V→Bool) (v : V) :
    guardSet E sgn (.inr (.inl v)) = {(.inr v,false),(.inl v,sgn v)} := by
  simp [guardSet,guardedClause]

@[simp] theorem guardSet_edge (E : Finset (V×V)) (sgn : V→Bool) (e : ↥E) :
    guardSet E sgn (.inr (.inr e)) = positiveEdge Sum.inl e.val := by
  simp [guardSet,guardedClause,positiveEdge]

theorem guarded_index_inclusion (E : Finset (V×V)) (h : OrientedSimple E)
    (sgn : V→Bool) {i j : GuardIndex E}
    (hs : guardSet E sgn i ⊆ guardSet E sgn j) : i=j := by
  rcases i with u|(u|e) <;> rcases j with v|(v|f)
  · have hh := hs (show (.inr u,true) ∈ guardSet E sgn (.inl u) by simp)
    simp at hh
    subst v
    rfl
  · have hh := hs (show (.inr u,true) ∈ guardSet E sgn (.inl u) by simp)
    simp at hh
  · have hh := hs (show (.inr u,true) ∈ guardSet E sgn (.inl u) by simp)
    simp [positiveEdge] at hh
  · have hh := hs (show (.inl u,sgn u) ∈ guardSet E sgn (.inr (.inl u)) by simp)
    simp at hh
  · have hh := hs (show (.inr u,false) ∈ guardSet E sgn (.inr (.inl u)) by simp)
    simp at hh
    subst v
    rfl
  · have hh := hs (show (.inr u,false) ∈ guardSet E sgn (.inr (.inl u)) by simp)
    simp [positiveEdge] at hh
  · have hh := hs (show (.inl e.val.1,true) ∈ guardSet E sgn (.inr (.inr e))
      by simp [positiveEdge])
    simp at hh
  · have eh1 : e.val.1=v ∧ sgn v=true := by
      have hh := hs (show (.inl e.val.1,true) ∈ guardSet E sgn (.inr (.inr e))
        by simp [positiveEdge])
      simpa using hh
    have eh2 : e.val.2=v ∧ sgn v=true := by
      have hh := hs (show (.inl e.val.2,true) ∈ guardSet E sgn (.inr (.inr e))
        by simp [positiveEdge])
      simpa using hh
    exact (oriented_distinct h e.property (eh1.1.trans eh2.1.symm)).elim
  · have heq : e.val=f.val := positive_edge_subset_eq h e.property f.property
      (Sum.inl : V→GuardVar V) Sum.inl_injective (by simpa using hs)
    have hEF : e=f := Subtype.ext heq
    subst f
    rfl

theorem guarded_set_injective (E : Finset (V×V)) (h : OrientedSimple E) (sgn : V→Bool) :
    Function.Injective (guardSet E sgn) := by
  intro i j he
  apply guarded_index_inclusion E h sgn
  rw [he]

omit [DecidableEq V] in
theorem guarded_clause_nodup (E : Finset (V×V)) (h : OrientedSimple E)
    (sgn : V→Bool) (i : GuardIndex E) : (guardedClause E sgn i).Nodup := by
  rcases i with v|(v|e)
  · simp [guardedClause]
  · simp [guardedClause]
  · simp [guardedClause,oriented_distinct h e.property]

theorem guarded_set_tautFree (E : Finset (V×V)) (sgn : V→Bool) (i : GuardIndex E) :
    TautFree (guardSet E sgn i) := by
  rcases i with v|(v|e)
  · simp [TautFree]
  · intro w
    cases w with
    | inl w => simp; tauto
    | inr w => simp
  · simpa only [guardSet_edge] using (positive_edge_tautFree (Sum.inl : V→GuardVar V) e.val)

theorem guarded_set_card (E : Finset (V×V)) (h : OrientedSimple E) (sgn : V→Bool)
    (i : GuardIndex E) :
    (guardSet E sgn i).card=match i with | .inl _ => 1 | .inr _ => 2 := by
  rcases i with v|(v|e)
  · simp
  · rw [guardSet_lock,Finset.card_pair]
    simp
  · simpa only [guardSet_edge] using
      (positive_edge_card h e.property (Sum.inl : V→GuardVar V) Sum.inl_injective)

theorem guarded_parsed_mem [Fintype V] (E : Finset (V×V)) (sgn : V→Bool)
    (C : ClauseSet (GuardVar V)) :
    C∈parsed (guardedFormula E sgn) ↔ ∃ i,guardSet E sgn i=C := by
  simp only [mem_parsed,guardedFormula,List.mem_map,Finset.mem_toList,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨L,⟨i,rfl⟩,hh⟩
    exact ⟨i,hh⟩
  · rintro ⟨i,hh⟩
    exact ⟨_,⟨i,rfl⟩,hh⟩

theorem guarded_family_eq_image [Fintype V] (E : Finset (V×V)) (sgn : V→Bool) :
    parsed (guardedFormula E sgn) = Finset.univ.image (guardSet E sgn) := by
  ext C
  simp [guarded_parsed_mem]

theorem guarded_parsed_card [Fintype V] (E : Finset (V×V)) (h : OrientedSimple E)
    (sgn : V→Bool) :
    (parsed (guardedFormula E sgn)).card=(guardedFormula E sgn).length := by
  rw [guarded_family_eq_image,Finset.card_image_of_injective _ (guarded_set_injective E h sgn),
    Finset.card_univ,guarded_length]
  simp [GuardIndex,Nat.two_mul]
  omega

theorem guarded_actual_nodup [Fintype V] (E : Finset (V×V)) (h : OrientedSimple E)
    (sgn : V→Bool) :
    (guardedFormula E sgn).Nodup ∧ ∀ L∈guardedFormula E sgn,L.Nodup := by
  have hi : Function.Injective (guardedClause E sgn) := by
    intro i j hh
    exact guarded_set_injective E h sgn (congrArg List.toFinset hh)
  refine ⟨Finset.nodup_toList _ |>.map hi,?_⟩
  intro L hL
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hL
  exact guarded_clause_nodup E h sgn i

theorem normalize_actual_guard [Fintype V] (E : Finset (V×V)) (h : OrientedSimple E)
    (sgn : V→Bool) :
    normalize (parsed (guardedFormula E sgn))=parsed (guardedFormula E sgn) := by
  apply normalization_fixed
  · intro C hC
    obtain ⟨i,rfl⟩ := (guarded_parsed_mem E sgn C).mp hC
    exact guarded_set_tautFree E sgn i
  · intro C hC D hD hs
    obtain ⟨i,rfl⟩ := (guarded_parsed_mem E sgn C).mp hC
    obtain ⟨j,rfl⟩ := (guarded_parsed_mem E sgn D).mp hD
    rw [guarded_index_inclusion E h sgn hs]

theorem guarded_literal_width [Fintype V] (E : Finset (V×V)) (h : OrientedSimple E)
    (sgn : V→Bool) {C : ClauseSet (GuardVar V)} (hC : C∈parsed (guardedFormula E sgn)) :
    C.card=1 ∨ C.card=2 := by
  obtain ⟨i,rfl⟩ := (guarded_parsed_mem E sgn C).mp hC
  cases i <;> simp [guarded_set_card E h]

#print axioms guardSet_unit
#print axioms guardSet_lock
#print axioms guardSet_edge
#print axioms guarded_index_inclusion
#print axioms guarded_set_injective
#print axioms guarded_clause_nodup
#print axioms guarded_set_tautFree
#print axioms guarded_set_card
#print axioms guarded_parsed_mem
#print axioms guarded_family_eq_image
#print axioms guarded_parsed_card
#print axioms guarded_actual_nodup
#print axioms normalize_actual_guard
#print axioms guarded_literal_width
end Paper5.FrontendG1.Normalization