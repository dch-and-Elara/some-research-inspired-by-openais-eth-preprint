import V8PooledRangeSplit

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

namespace V8PooledRange

def SameEnds {V E : Type*} (G : Graph V E) (e f : E) : Prop :=
  (G e false = G f false ∧ G e true = G f true) ∨
  (G e false = G f true ∧ G e true = G f false)

structure IsSimple {V E : Type*} (G : Graph V E) : Prop where
  loopless : ∀ e, G e false ≠ G e true
  edge_unique : ∀ e f, SameEnds G e f → e=f

private theorem tree_cases (k : ℕ) (j : TreeEdge k) :
    (∃ i, j=privateLeafEdge k i) ∨ (∃ i, j=neighboringSpineEdge k i) := by
  have h := treeEdge_ofKind k j
  rcases hj : treeEdgeKind k j with (i | i)
  · exact Or.inl ⟨i, (by simpa only [hj,Sum.elim_inl] using h.symm)⟩
  · exact Or.inr ⟨i, (by simpa only [hj,Sum.elim_inr] using h.symm)⟩

theorem tree_simple (k : ℕ) : IsSimple (treeEnds k) := by
  refine ⟨?_,?_⟩
  · intro e
    rcases tree_cases k e with (⟨i,rfl⟩ | ⟨i,rfl⟩)
    · simp
    · intro h
      have hh := congrArg (fun x : Tree k => x.1.val) h
      rw [treeEnd_spine,treeEnd_spine] at hh
      change i.val = i.val+1 at hh
      omega
  · intro e f h
    rcases tree_cases k e with (⟨i,rfl⟩ | ⟨i,rfl⟩) <;>
      rcases tree_cases k f with (⟨j,rfl⟩ | ⟨j,rfl⟩)
    · unfold SameEnds at h
      simp only [treeEnd_leaf,Prod.mk.injEq,Bool.false_eq_true,Bool.true_eq_false, and_false,
        and_self, and_true, or_false] at h
      rw [h]
    · unfold SameEnds at h
      simp [treeEnd_leaf,treeEnd_spine] at h
    · unfold SameEnds at h
      simp [treeEnd_leaf,treeEnd_spine] at h
    · unfold SameEnds at h
      simp only [treeEnd_spine,Bool.false_eq_true,↓reduceIte,Prod.mk.injEq,and_true] at h
      rcases h with (⟨h,_⟩ | ⟨h₀,h₁⟩)
      · have hh : i = j := Fin.castSucc_injective _ h
        rw [hh]
      · have hi := congrArg Fin.val h₀
        have hj := congrArg Fin.val h₁
        change i.val = j.val + 1 at hi
        change i.val + 1 = j.val at hj
        omega

namespace Split

@[simp] theorem tree_endpoint {k : ℕ} {E : Type*} (H : Graph (Deficit k) E)
    (p : ThreePorts H) (i : TreeEdge k) (b : Bool) :
    graph H p (.inl i) b = Sum.inl (treeEnds k i b) := rfl

@[simp] theorem old_endpoint {k : ℕ} {E : Type*} (H : Graph (Deficit k) E)
    (p : ThreePorts H) (i : E) (b : Bool) :
    graph H p (.inr (.inl i)) b = Sum.inr (H i b,coreHalf (sourceIndex H p i b)) := rfl

@[simp] theorem link_endpoint {k : ℕ} {E : Type*} (H : Graph (Deficit k) E)
    (p : ThreePorts H) (c : Deficit k) (b : Bool) :
    graph H p (.inr (.inr (.inl c))) b = Sum.inr (c,b) := rfl

@[simp] theorem spoke_endpoint_tree {k : ℕ} {E : Type*} (H : Graph (Deficit k) E)
    (p : ThreePorts H) (c : Deficit k) :
    graph H p (.inr (.inr (.inr c))) false = Sum.inl (deficitTarget k c) := rfl

@[simp] theorem spoke_endpoint_core {k : ℕ} {E : Type*} (H : Graph (Deficit k) E)
    (p : ThreePorts H) (c : Deficit k) :
    graph H p (.inr (.inr (.inr c))) true = Sum.inr (c,true) := rfl

theorem isSimple {k : ℕ} {E : Type*} (H : Graph (Deficit k) E) (p : ThreePorts H)
    (h : IsSimple H) : IsSimple (graph H p) := by
  refine ⟨?_,?_⟩
  · intro e
    rcases e with (e | (e | (c | c)))
    · intro he
      exact (tree_simple k).loopless e (Sum.inl.inj he)
    · intro he
      exact h.loopless e (congrArg Prod.fst (Sum.inr.inj he))
    · simp
    · simp
  · intro e f hr
    rcases e with (x | (x | (x | x))) <;> rcases f with (y | (y | (y | y))) <;>
      simp [SameEnds] at hr ⊢
    · exact (tree_simple k).edge_unique x y hr
    · rcases hr with (⟨⟨h0,_⟩,h1,_⟩ | ⟨⟨h0,_⟩,h1,_⟩)
      · exact h.edge_unique x y (Or.inl ⟨h0,h1⟩)
      · exact h.edge_unique x y (Or.inr ⟨h0,h1⟩)
    · rcases hr with (⟨⟨h0,_⟩,h1,_⟩ | ⟨⟨h0,_⟩,h1,_⟩) <;>
        exact False.elim (h.loopless x (h0.trans h1.symm))
    · rcases hr with (⟨⟨h0,_⟩,h1,_⟩ | ⟨⟨h0,_⟩,h1,_⟩)
      · exact False.elim (h.loopless y (h0.symm.trans h1))
      · exact False.elim (h.loopless y (h1.symm.trans h0))
    · exact hr
    · exact hr.2

#print axioms tree_simple
#print axioms isSimple

end Split
end V8PooledRange
