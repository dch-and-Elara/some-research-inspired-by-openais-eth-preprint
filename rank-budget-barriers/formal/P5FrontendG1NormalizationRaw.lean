import P5FrontendG1NormalizationCore

/-! Stored, singly oriented simple edges and the unchanged normalization
of literal signed units plus uncovered positive edges. -/
namespace Paper5.FrontendG1.Normalization

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- Each edge is stored once in just one of its two possible orientations. -/
def OrientedSimple (E : Finset (V×V)) : Prop :=
  ∀ e∈E, e.swap ∉ E

omit [DecidableEq V] in
theorem oriented_distinct {E : Finset (V×V)} (h : OrientedSimple E)
    {e : V×V} (he : e∈E) : e.1 ≠ e.2 := by
  intro hEq
  have hs : e.swap=e := Prod.ext hEq.symm hEq
  exact h e he (hs.symm ▸ he)

def positiveEdge (ι : V→W) (e : V×V) : ClauseSet W :=
  {(ι e.1,true),(ι e.2,true)}

omit [DecidableEq V] in
theorem positive_edge_card {E : Finset (V×V)} (h : OrientedSimple E)
    {e : V×V} (he : e∈E) (ι : V→W) (hi : Function.Injective ι) :
    (positiveEdge ι e).card=2 := by
  apply Finset.card_pair
  intro hh
  exact oriented_distinct h he (hi (congrArg Prod.fst hh))

omit [DecidableEq V] in
theorem positive_edge_subset_eq {E : Finset (V×V)} (h : OrientedSimple E)
    {e f : V×V} (he : e∈E) (hf : f∈E) (ι : V→W) (hi : Function.Injective ι)
    (hs : positiveEdge ι e ⊆ positiveEdge ι f) : e=f := by
  have hu : e.1=f.1 ∨ e.1=f.2 := by
    have hh := hs (show (ι e.1,true)∈positiveEdge ι e by simp [positiveEdge])
    simpa [positiveEdge,hi.eq_iff] using hh
  have hv : e.2=f.1 ∨ e.2=f.2 := by
    have hh := hs (show (ι e.2,true)∈positiveEdge ι e by simp [positiveEdge])
    simpa [positiveEdge,hi.eq_iff] using hh
  rcases hu with hu|hu <;> rcases hv with hv|hv
  · exact (oriented_distinct h he (hu.trans hv.symm)).elim
  · exact Prod.ext hu hv
  · exact (h e he ((show e.swap=f from Prod.ext hv hu).symm ▸ hf)).elim
  · exact (oriented_distinct h he (hu.trans hv.symm)).elim

omit [DecidableEq V] in
theorem positive_edge_tautFree (ι : V→W) (e : V×V) :
    TautFree (positiveEdge ι e) := by
  simp [TautFree,positiveEdge]

section Raw
variable [Fintype V]

def rawUnit (sgn : V→Bool) (v : V) : ClauseSet V := {(v,sgn v)}

theorem mem_raw_family (E : Finset (V×V)) (sgn : V→Bool) (C : ClauseSet V) :
    C∈parsed (PinnedCNF.formula E sgn) ↔
      (∃ v,rawUnit sgn v=C) ∨ ∃ e∈E,positiveEdge id e=C := by
  simp only [mem_parsed,PinnedCNF.formula,List.mem_append,List.mem_map,Finset.mem_toList,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨L,(⟨v,rfl⟩|⟨e,he,rfl⟩),hh⟩
    · exact Or.inl ⟨v,by simpa [rawUnit] using hh⟩
    · exact Or.inr ⟨e,he,by simpa [positiveEdge] using hh⟩
  · rintro (⟨v,hh⟩|⟨e,he,hh⟩)
    · exact ⟨_,Or.inl ⟨v,rfl⟩,by simpa [rawUnit] using hh⟩
    · exact ⟨_,Or.inr ⟨e,he,rfl⟩,by simpa [positiveEdge] using hh⟩

theorem raw_family_nonempty_tautFree (E : Finset (V×V)) (sgn : V→Bool)
    (C : ClauseSet V) (hC : C∈parsed (PinnedCNF.formula E sgn)) :
    C.Nonempty ∧ TautFree C := by
  rcases (mem_raw_family E sgn C).mp hC with ⟨v,rfl⟩|⟨e,_,rfl⟩
  · cases hs : sgn v <;> simp [rawUnit,TautFree,hs]
  · exact ⟨⟨(e.1,true),by simp [positiveEdge]⟩,positive_edge_tautFree id e⟩

theorem raw_keep_unit (E : Finset (V×V)) (sgn : V→Bool) (v : V) :
    rawUnit sgn v∈normalize (parsed (PinnedCNF.formula E sgn)) := by
  have hm : rawUnit sgn v∈parsed (PinnedCNF.formula E sgn) :=
    (mem_raw_family E sgn _).mpr (Or.inl ⟨v,rfl⟩)
  refine (mem_normalize _ _).mpr ⟨hm,(raw_family_nonempty_tautFree E sgn _ hm).2,?_⟩
  rintro ⟨D,hD,_,hs⟩
  have hem : D=∅ := Finset.ssubset_singleton_iff.mp hs
  exact (raw_family_nonempty_tautFree E sgn D hD).1.ne_empty hem

omit [Fintype V] in
theorem raw_unit_subset_positive (sgn : V→Bool) (v : V) (e : V×V) :
    rawUnit sgn v ⊆ positiveEdge id e ↔
      sgn v=true ∧ (v=e.1 ∨ v=e.2) := by
  simp [rawUnit,positiveEdge,Finset.singleton_subset_iff]
  tauto

/-- In the actual raw normalized formula the edge survives exactly when
both stored endpoint signs are zero. -/
theorem raw_keep_edge_iff (E : Finset (V×V)) (h : OrientedSimple E) (sgn : V→Bool)
    (e : V×V) (he : e∈E) :
    positiveEdge id e∈normalize (parsed (PinnedCNF.formula E sgn)) ↔
      sgn e.1=false ∧ sgn e.2=false := by
  have hc := positive_edge_card h he id Function.injective_id
  have hpos {v : V} (hv : sgn v=true) (hve : v=e.1 ∨ v=e.2) :
      rawUnit sgn v ⊂ positiveEdge id e := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨(raw_unit_subset_positive sgn v e).mpr ⟨hv,hve⟩,?_⟩
    intro ht
    have hh := congrArg Finset.card ht
    simp [rawUnit,hc] at hh
  rw [mem_normalize]
  constructor
  · rintro ⟨_,_,hs⟩
    have hp (v : V) (hv : v=e.1 ∨ v=e.2) : sgn v=false := by
      cases hsgn : sgn v with
      | false => rfl
      | true =>
        have hm := (mem_raw_family E sgn (rawUnit sgn v)).mpr (Or.inl ⟨v,rfl⟩)
        exact (hs ⟨_,hm,(raw_family_nonempty_tautFree E sgn _ hm).2,hpos hsgn hv⟩).elim
    exact ⟨hp e.1 (Or.inl rfl),hp e.2 (Or.inr rfl)⟩
  · rintro ⟨h1,h2⟩
    refine ⟨(mem_raw_family E sgn _).mpr (Or.inr ⟨e,he,rfl⟩),positive_edge_tautFree id e,?_⟩
    rintro ⟨D,hD,_,hs⟩
    rcases (mem_raw_family E sgn D).mp hD with ⟨v,rfl⟩|⟨f,hf,rfl⟩
    · obtain ⟨hv,hve⟩ := (raw_unit_subset_positive sgn v e).mp hs.subset
      rcases hve with hv'|hv' <;> subst v <;> simp_all
    · have hlt := Finset.card_lt_card hs
      rw [positive_edge_card h hf id Function.injective_id,hc] at hlt
      omega

def survivingEdges (E : Finset (V×V)) (sgn : V→Bool) : Finset (V×V) :=
  E.filter fun e=>sgn e.1=false ∧ sgn e.2=false

theorem normalize_actual_raw (E : Finset (V×V)) (h : OrientedSimple E)
    (sgn : V→Bool) :
    normalize (parsed (PinnedCNF.formula E sgn)) =
      parsed (PinnedCNF.formula (survivingEdges E sgn) sgn) := by
  ext C
  rw [mem_raw_family]
  constructor
  · intro hC
    obtain ⟨hm,_,_⟩ := (mem_normalize _ _).mp hC
    rcases (mem_raw_family E sgn C).mp hm with ⟨v,rfl⟩|⟨e,he,rfl⟩
    · exact Or.inl ⟨v,rfl⟩
    · exact Or.inr ⟨e,Finset.mem_filter.mpr ⟨he,(raw_keep_edge_iff E h sgn e he).mp hC⟩,rfl⟩
  · rintro (⟨v,rfl⟩|⟨e,he,rfl⟩)
    · exact raw_keep_unit E sgn v
    · obtain ⟨he,hb⟩ := Finset.mem_filter.mp he
      exact (raw_keep_edge_iff E h sgn e he).mpr hb

omit [Fintype V] [DecidableEq V] in
theorem surviving_empty_iff (E : Finset (V×V)) (sgn : V→Bool) :
    survivingEdges E sgn=∅ ↔ PinnedCNF.AllEdges E sgn := by
  rw [Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h e he
    by_cases h1 : sgn e.1=true
    · exact Or.inl h1
    · apply Or.inr
      by_contra h2
      exact h e (Finset.mem_filter.mpr ⟨he,Bool.eq_false_of_not_eq_true h1,
        Bool.eq_false_of_not_eq_true h2⟩)
  · intro h e
    rintro hm
    obtain ⟨he,h1,h2⟩ := Finset.mem_filter.mp hm
    simpa [h1,h2] using h e he

omit [DecidableEq V] in
theorem raw_count_one_iff_no_edge (E : Finset (V×V)) (sgn : V→Bool) :
    PinnedCNF.modelCount (PinnedCNF.formula E sgn)=1 ↔ survivingEdges E sgn=∅ := by
  classical
  rw [PinnedCNF.count_eq_indicator,surviving_empty_iff]
  split_ifs <;> simp_all

#print axioms oriented_distinct
#print axioms positive_edge_card
#print axioms positive_edge_subset_eq
#print axioms positive_edge_tautFree
#print axioms mem_raw_family
#print axioms raw_family_nonempty_tautFree
#print axioms raw_keep_unit
#print axioms raw_unit_subset_positive
#print axioms raw_keep_edge_iff
#print axioms normalize_actual_raw
#print axioms surviving_empty_iff
#print axioms raw_count_one_iff_no_edge

end Raw
end Paper5.FrontendG1.Normalization