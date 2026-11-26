import P5MainIteratorSourceLayout

/-! Manufacture the physical copy chart directly from literal factor
scopes and the full-cell cap. The source premise that each assignment
variable occurs can also be supplied by the neutral singleton factors. -/
namespace P5MainIterator
open scoped BigOperators Classical

variable {V F I B : Type*} [Fintype V] [Fintype F] [Fintype I] [Fintype B] [LinearOrder B]

abbrev ScopeIncidence (scope : F → Finset V) := Σ f : F, {v : V // v∈scope f}

def scopeCell (scope : F → Finset V) (a : V→I→B) (d : F→I→B)
    (e : ScopeIncidence scope) : WordCell I B :=
  fun i => (a e.2.val i,d e.1 i)

abbrev cellFiber (scope : F → Finset V) (a : V→I→B) (d : F→I→B)
    (u : WordCell I B) :=
  {e : ScopeIncidence scope // scopeCell scope a d e=u}

noncomputable def sourceCopyBudget (scope : F → Finset V) : ℕ :=
  (2*Fintype.card (ScopeIncidence scope))/Fintype.card (WordCell I B)

omit [Fintype V] [Fintype F] [Fintype I] [Fintype B] [LinearOrder B] in
theorem scope_occurs (scope : F→Finset V) (h : ∀ v,∃ f,v∈scope f) :
    Function.Surjective (fun e : ScopeIncidence scope => e.2.val) := by
  intro v
  obtain ⟨f,hf⟩ := h v
  exact ⟨⟨f,⟨v,hf⟩⟩,rfl⟩

omit [Fintype V] [Fintype B] in
private theorem same_fiber_index (scope : F→Finset V) (a : V→I→B) (d : F→I→B)
    (e : ScopeIncidence scope) (u : WordCell I B) (he : scopeCell scope a d e=u) :
    (Fintype.equivFin (cellFiber scope a d (scopeCell scope a d e)) ⟨e,rfl⟩).val =
    (Fintype.equivFin (cellFiber scope a d u) ⟨e,he⟩).val := by subst u; rfl

noncomputable def allocateScopeCopies (scope : F→Finset V) (a : V→I→B) (d : F→I→B)
    (H : ℕ) (h : ∀ u, Fintype.card (cellFiber scope a d u)≤H) :
    ScopeIncidence scope ↪ (Fin H × WordCell I B) where
  toFun e := ⟨Fin.castLE (h (scopeCell scope a d e))
      (Fintype.equivFin (cellFiber scope a d (scopeCell scope a d e)) ⟨e,rfl⟩),
    scopeCell scope a d e⟩
  inj' := by
    intro e f hEq
    have hu : scopeCell scope a d e=scopeCell scope a d f := congrArg Prod.snd hEq
    let u := scopeCell scope a d e
    have h₁ : (⟨e,rfl⟩ : cellFiber scope a d u) = ⟨f,hu.symm⟩ := by
      apply (Fintype.equivFin (cellFiber scope a d u)).injective
      apply Fin.ext
      have he : (Fintype.equivFin (cellFiber scope a d u) ⟨e,rfl⟩).val =
          (Fintype.equivFin (cellFiber scope a d (scopeCell scope a d f)) ⟨f,rfl⟩).val :=
        congrArg (fun p : Fin H × WordCell I B => p.1.val) hEq
      exact he.trans (same_fiber_index scope a d f u hu.symm)
    exact congrArg Subtype.val h₁

noncomputable def fromActualScopes (scope : F→Finset V) (a : V→I→B) (d : F→I→B)
    (H : ℕ) (h : ∀ u, Fintype.card (cellFiber scope a d u)≤H)
    (hOccurs : ∀ v,∃ f,v∈scope f) :
    SourceLayout (ScopeIncidence scope) V F (Fin H) I B where
  placement := ⟨fun e=>e.2.val,allocateScopeCopies scope a d H h,scope_occurs scope hOccurs⟩
  factor := Sigma.fst
  a := a
  d := d
  first _ _ := rfl
  second _ _ := rfl

set_option linter.unusedSectionVars false in
theorem scoped_cellLoad_exact (scope : F→Finset V) (a : V→I→B) (d : F→I→B)
    (H : ℕ) (h : ∀ u, Fintype.card (cellFiber scope a d u)≤H)
    (hOccurs : ∀ v,∃ f,v∈scope f) (u : WordCell I B) :
    cellLoad (fromActualScopes scope a d H h hOccurs) u=Fintype.card (cellFiber scope a d u) := by
  unfold cellLoad cellFiber
  rw [Fintype.card_subtype]
  apply congrArg Finset.card
  ext e
  simp [fromActualScopes,allocateScopeCopies]

omit [Fintype V] in
theorem native_copy_budget (scope : F→Finset V) (a : V→I→B) (d : F→I→B) [Nonempty B]
    (h : ∀ u, Fintype.card (cellFiber scope a d u)*Fintype.card (WordCell I B)≤2*Fintype.card (ScopeIncidence scope)) :
    ∀ u, Fintype.card (cellFiber scope a d u)≤sourceCopyBudget (I:=I) (B:=B) scope := by
  intro u
  apply (Nat.le_div_iff_mul_le (show 0<Fintype.card (WordCell I B) from Fintype.card_pos)).mpr
  exact h u

#print axioms scope_occurs
#print axioms allocateScopeCopies
#print axioms scoped_cellLoad_exact
#print axioms native_copy_budget
end P5MainIterator
