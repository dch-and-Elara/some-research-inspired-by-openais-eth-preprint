import RootEntry

/-! Section 3 of the fourth-paper bridge. Clause sets are used for the
containment pass, while the direct fixed-density entry uses RootEntry's CNF. -/

namespace RootSeparation.Preprocessing

open Finset GraphCutMoments
open scoped BigOperators
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Lit (V : Type*) := V × Bool

def clauseSets (F : Std.Sat.CNF V) : Finset (Finset (Lit V)) :=
  (F.map List.toFinset).toFinset

def antichain (S : Finset (Finset (Lit V))) : Finset (Finset (Lit V)) :=
  S.filter fun C => ¬ ∃ D ∈ S, D ⊂ C

noncomputable def normalized (F : Std.Sat.CNF V) : Finset (Finset (Lit V)) :=
  antichain (clauseSets (Entry.simpleNormalize F))

lemma mem_clauseSets (E : Finset (V × V)) (σ : V → Bool) (C : Finset (Lit V)) :
    C ∈ clauseSets (PinnedCNF.formula E σ) ↔
      ∃ i, (Entry.clause E σ i).toFinset = C := by
  simp only [clauseSets, List.mem_toFinset, List.mem_map, Entry.clause_mem]
  constructor
  · rintro ⟨_,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨_,⟨i,rfl⟩,rfl⟩

lemma clause_card (E : Finset (V × V)) (h : Entry.Simple E) (σ : V → Bool)
    (i : Entry.Clause E) :
    (Entry.clause E σ i).toFinset.card = match i with | .inl _ => 1 | .inr _ => 2 := by
  cases i with
  | inl v => simp [Entry.clause]
  | inr e =>
    have hn := h.loopless e.val e.property
    simp [Entry.clause, Finset.card_insert_of_notMem, hn]

lemma pin_kept (E : Finset (V × V)) (h : Entry.Simple E) (σ : V → Bool) (v : V) :
    (Entry.clause E σ (.inl v)).toFinset ∈ antichain (clauseSets (PinnedCNF.formula E σ)) := by
  refine mem_filter.mpr ⟨(mem_clauseSets E σ _).mpr ⟨_,rfl⟩,?_⟩
  rintro ⟨D,hD,hs⟩
  obtain ⟨i,rfl⟩ := (mem_clauseSets E σ D).mp hD
  have hlt := card_lt_card hs
  rw [clause_card E h σ, clause_card E h σ] at hlt
  cases i <;> simp at hlt

lemma edge_kept_iff (E : Finset (V × V)) (h : Entry.Simple E) (σ : V → Bool) (e : E) :
    (Entry.clause E σ (.inr e)).toFinset ∈ antichain (clauseSets (PinnedCNF.formula E σ))
      ↔ e.val ∈ Entry.survivingEdges E σ := by
  rw [Entry.survives_iff]
  constructor
  · intro he
    rintro ⟨v,hsub⟩
    have hne : (Entry.clause E σ (.inl v)).toFinset ≠ (Entry.clause E σ (.inr e)).toFinset := by
      intro hh
      exact (by decide : (1:ℕ) ≠ 2) (by simpa only [clause_card E h σ] using congrArg Finset.card hh)
    exact (mem_filter.mp he).2 ⟨_,(mem_clauseSets E σ _).mpr ⟨_,rfl⟩,Finset.ssubset_iff_subset_ne.mpr ⟨hsub,hne⟩⟩
  · intro he
    refine mem_filter.mpr ⟨(mem_clauseSets E σ _).mpr ⟨_,rfl⟩,?_⟩
    rintro ⟨D,hD,hs⟩
    obtain ⟨i,rfl⟩ := (mem_clauseSets E σ D).mp hD
    cases i with
    | inl v => exact he ⟨v,hs.subset⟩
    | inr f =>
      have hlt := card_lt_card hs
      rw [clause_card E h σ, clause_card E h σ] at hlt
      simp at hlt

/-- The main/general-reduction pass retains exactly all pins and the positive
edge clauses whose two pins are negative. This is a clause-set identity. -/
theorem normalize_pinned (E : Finset (V × V)) (h : Entry.Simple E) (σ : V → Bool) :
    normalized (PinnedCNF.formula E σ) =
      clauseSets (PinnedCNF.formula (Entry.survivingEdges E σ) σ) := by
  unfold normalized
  rw [Entry.simpleNormalize_pinned E h σ]
  ext C
  constructor
  · intro hC
    obtain ⟨i,rfl⟩ := (mem_clauseSets E σ C).mp (mem_filter.mp hC).1
    cases i with
    | inl v => exact (mem_clauseSets _ σ _).mpr ⟨.inl v,rfl⟩
    | inr e =>
      have he := (edge_kept_iff E h σ e).mp hC
      exact (mem_clauseSets _ σ _).mpr ⟨.inr ⟨e.val,he⟩,rfl⟩
  · intro hC
    obtain ⟨i,rfl⟩ := (mem_clauseSets (Entry.survivingEdges E σ) σ C).mp hC
    cases i with
    | inl v => exact pin_kept E h σ v
    | inr e =>
      have he : e.val ∈ E := (mem_filter.mp e.property).1
      exact (edge_kept_iff E h σ ⟨e.val,he⟩).mpr e.property

lemma surviving_subset (E : Finset (V × V)) (σ : V → Bool) :
    Entry.survivingEdges E σ ⊆ E := filter_subset _ _

lemma surviving_simple (E : Finset (V × V)) (h : Entry.Simple E) (σ : V → Bool) :
    Entry.Simple (Entry.survivingEdges E σ) where
  loopless e he := h.loopless e (surviving_subset E σ he)
  oriented u v he hn := h.oriented u v (surviving_subset E σ he) (surviving_subset E σ hn)

theorem surviving_degree (E : Finset (V × V)) (σ : V → Bool) (v : V) :
    degree (Entry.survivingEdges E σ) v ≤ degree E v := by
  unfold degree
  exact Nat.add_le_add
    (card_le_card (filter_subset_filter _ (surviving_subset E σ)))
    (card_le_card (filter_subset_filter _ (surviving_subset E σ)))

theorem sat_normalized_iff (E : Finset (V × V)) (σ x : V → Bool) :
    Std.Sat.CNF.Sat x (PinnedCNF.formula (Entry.survivingEdges E σ) σ) ↔
      Std.Sat.CNF.Sat x (PinnedCNF.formula E σ) := by
  rw [PinnedCNF.sat_iff, PinnedCNF.sat_iff]
  refine and_congr_right fun _ => ⟨?_,?_⟩
  · intro h e he
    cases h₁ : σ e.1
    · cases h₂ : σ e.2
      · simpa only [h₁,h₂] using h e (mem_filter.mpr ⟨he,h₁,h₂⟩)
      · exact Or.inr rfl
    · exact Or.inl rfl
  · exact fun h e he => h e (surviving_subset E σ he)

theorem allEdges_iff_surviving_empty (E : Finset (V × V)) (σ : V → Bool) :
    PinnedCNF.AllEdges E σ ↔ Entry.survivingEdges E σ = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  constructor
  · intro hs e he
    obtain ⟨he',h₁,h₂⟩ := mem_filter.mp he
    simpa [h₁,h₂] using hs e he'
  · intro hs e he
    cases h₁ : σ e.1
    · cases h₂ : σ e.2
      · exact (hs e (mem_filter.mpr ⟨he,h₁,h₂⟩)).elim
      · exact Or.inr rfl
    · exact Or.inl rfl

/-- Fully substituting the pinned values leaves an empty clause for each
unsatisfied input clause, and deletes each satisfied clause. -/
noncomputable def afterPropagatingPins (E : Finset (V × V)) (σ : V → Bool) : Std.Sat.CNF V :=
  (PinnedCNF.formula E σ).filterMap fun c =>
    if c.any (fun l => σ l.1 == l.2) then none else some []

theorem propagated_has_empty (E : Finset (V × V)) (σ : V → Bool) :
    [] ∈ afterPropagatingPins E σ ↔ ¬ PinnedCNF.AllEdges E σ := by
  unfold afterPropagatingPins
  rw [List.mem_filterMap, allEdges_iff_surviving_empty]
  change _ ↔ Entry.survivingEdges E σ ≠ ∅
  rw [← nonempty_iff_ne_empty]
  constructor
  · rintro ⟨c,hc,he⟩
    obtain ⟨i,rfl⟩ := (Entry.clause_mem E σ c).mp hc
    cases i with
    | inl v => simp [Entry.clause] at he
    | inr e =>
      refine ⟨e.val,mem_filter.mpr ⟨e.property,?_⟩⟩
      cases h₁ : σ e.val.1 <;> cases h₂ : σ e.val.2 <;>
        simp [Entry.clause,h₁,h₂] at he ⊢
  · rintro ⟨e,he⟩
    obtain ⟨hE,h₁,h₂⟩ := mem_filter.mp he
    let i : Entry.Clause E := .inr ⟨e,hE⟩
    refine ⟨Entry.clause E σ i,(Entry.clause_mem E σ _).mpr ⟨i,rfl⟩,?_⟩
    simp [i,Entry.clause,h₁,h₂]

theorem normalized_clause_count (E : Finset (V × V)) (h : Entry.Simple E) (σ : V → Bool) :
    (normalized (PinnedCNF.formula E σ)).card = Fintype.card V+(Entry.survivingEdges E σ).card := by
  classical
  rw [normalize_pinned E h σ]
  let E' := Entry.survivingEdges E σ
  have heq : clauseSets (PinnedCNF.formula E' σ) =
      univ.image (fun i : Entry.Clause E' => (Entry.clause E' σ i).toFinset) := by
    ext C
    simp [mem_clauseSets]
  rw [heq, card_image_of_injective _ (Entry.clause_distinct E' (surviving_simple E h σ) σ)]
  simp [Entry.Clause,E']

/-- The source equality tree has one internal link only when the
variable has four ports, i.e. one pin plus three retained edge clauses. -/
abbrev Split (E : Finset (V × V)) := {v : V // degree E v = 3}
abbrev BuiltLink (E : Finset (V × V)) := S8.Uncloned.Incidence E ⊕ Split E
abbrev BuiltWire (E : Finset (V × V)) := BuiltLink E × Bool

def triple (E : Finset (V × V)) : ℕ := (univ.filter fun v => degree E v = 3).card

def builtM (E : Finset (V × V)) : ℕ := Fintype.card (BuiltWire E)

theorem builtM_eq (E : Finset (V × V)) :
    builtM E = 2*(Fintype.card V + 2*E.card + triple E) := by
  unfold builtM
  simp [BuiltWire, BuiltLink, Split, S8.Uncloned.Incidence, Fintype.card_subtype, triple]
  omega

def builtPin (E : Finset (V × V)) : V ↪ BuiltWire E where
  toFun v := (.inl (.inl v), true)
  inj' := by simp [Function.Injective]

theorem built_cubic (E : Finset (V × V)) (h : ∀ v, degree E v = 3) :
    builtM E = 10*Fintype.card V := by
  have he := regular_edge_count E 3 h
  rw [builtM_eq]
  simp [triple,h]
  omega

theorem built_allPositive (E : Finset (V × V)) :
    builtM (Entry.survivingEdges E (fun _ => true)) = 2*Fintype.card V := by
  rw [Entry.allPositive_subsumption, builtM_eq]
  simp [triple,degree]

theorem built_normalized_bounds (E : Finset (V × V)) (σ : V → Bool)
    (h : ∀ v, degree E v = 3) :
    Entry.size (Entry.survivingEdges E σ) ≤ builtM (Entry.survivingEdges E σ) ∧
    builtM (Entry.survivingEdges E σ) ≤ 3*Entry.size (Entry.survivingEdges E σ) := by
  have he := regular_edge_count E 3 h
  have he' := card_le_card (surviving_subset E σ)
  have ht : triple (Entry.survivingEdges E σ) ≤ Fintype.card V := by
    simpa [triple] using card_le_univ (univ.filter (fun v : V => degree (Entry.survivingEdges E σ) v = 3))
  rw [builtM_eq]
  unfold Entry.size Entry.m Entry.n
  omega

#print axioms normalize_pinned
#print axioms surviving_degree
#print axioms sat_normalized_iff
#print axioms propagated_has_empty
#print axioms normalized_clause_count
#print axioms builtM_eq
#print axioms built_cubic
#print axioms built_allPositive
#print axioms built_normalized_bounds

end RootSeparation.Preprocessing


