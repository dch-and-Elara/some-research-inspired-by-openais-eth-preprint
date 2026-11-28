import V8PooledRangeCNFSyntax

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace V8PooledRange

private def PairAgree {X : Type*} (a b : X × X) : Prop :=
  (a.1=b.1 ∧ a.2=b.2) ∨ (a.1=b.2 ∧ a.2=b.1)

private theorem PairAgree.symm {X : Type*} {a b : X × X} (h : PairAgree a b) : PairAgree b a := by
  rcases h with (⟨h0,h1⟩ | ⟨h0,h1⟩)
  · exact Or.inl ⟨h0.symm,h1.symm⟩
  · exact Or.inr ⟨h1.symm,h0.symm⟩

private theorem agree_of_support_eq {X : Type*} [DecidableEq X]
    (a b c d : X) (hne : a ≠ b) (h : ({a,b} : Finset X) = {c,d}) :
    PairAgree (a,b) (c,d) := by
  have h0 : a ∈ ({c,d} : Finset X) := h ▸ (by simp)
  have h1 : b ∈ ({c,d} : Finset X) := h ▸ (by simp)
  simp only [Finset.mem_insert,Finset.mem_singleton] at h0 h1
  rcases h0 with (ha | ha) <;> rcases h1 with (hb | hb)
  · exact False.elim (hne (ha.trans hb.symm))
  · exact Or.inl ⟨ha,hb⟩
  · exact Or.inr ⟨ha,hb⟩
  · exact False.elim (hne (ha.trans hb.symm))

private def pairOf {V E : Type*}
    (G : Graph V E) (p : ThreePorts G) (s : V → Bool) (i : ClauseId V E) :
    Variable V × Variable V := ((clauses G p s i).1.1,(clauses G p s i).2.1)

private theorem badCycleReverse (i j : Fin 5) : ¬(i=j+1 ∧ i+1=j) := by decide +revert
private theorem badCycleSwitch (i : Fin 5) :
    ¬((i=0 ∧ i+1=2) ∨ (i=2 ∧ i+1=0)) := by decide +revert

private theorem cycle_cycle {V E : Type*} (G : Graph V E) (p : ThreePorts G) (s : V → Bool)
    (v w : V) (i j : Fin 5)
    (h : PairAgree (pairOf G p s (.inl (.inl (v,i)))) (pairOf G p s (.inl (.inl (w,j))))) :
    (v,i) = (w,j) := by
  change PairAgree (Sum.inl (v,i),Sum.inl (v,i+1)) (Sum.inl (w,j),Sum.inl (w,j+1)) at h
  simp only [PairAgree,Sum.inl.injEq,Prod.mk.injEq] at h
  rcases h with (⟨⟨hv,hi⟩,_⟩ | ⟨⟨_,h0⟩,_,h1⟩)
  · exact Prod.ext hv hi
  · exact False.elim (badCycleReverse i j ⟨h0,h1⟩)

private theorem cycle_switch {V E : Type*} (G : Graph V E) (p : ThreePorts G) (s : V → Bool)
    (v w : V) (i : Fin 5)
    (h : PairAgree (pairOf G p s (.inl (.inl (v,i)))) (pairOf G p s (.inl (.inr w)))) :
    False := by
  change PairAgree (Sum.inl (v,i),Sum.inl (v,i+1)) (Sum.inl (w,0),Sum.inl (w,2)) at h
  simp only [PairAgree,Sum.inl.injEq,Prod.mk.injEq] at h
  rcases h with (⟨⟨_,h0⟩,_,h1⟩ | ⟨⟨_,h0⟩,_,h1⟩)
  · exact badCycleSwitch i (Or.inl ⟨h0,h1⟩)
  · exact badCycleSwitch i (Or.inr ⟨h0,h1⟩)

private theorem local_conflict {V E : Type*} (G : Graph V E) (p : ThreePorts G)
    (hloop : ∀ e, G e false ≠ G e true) (v : V) (e : E) (i j : Fin 5)
    (h : PairAgree (Sum.inl (v,i),Sum.inl (v,j)) (graphPort G p e false,graphPort G p e true)) :
    False := by
  simp only [PairAgree,graphPort,Sum.inl.injEq,Prod.mk.injEq] at h
  rcases h with (⟨⟨h0,_⟩,h1,_⟩ | ⟨⟨h0,_⟩,h1,_⟩)
  · exact hloop e (h0.symm.trans h1)
  · exact hloop e (h1.symm.trans h0)

private theorem conflict_conflict {V E : Type*} (G : Graph V E) (p : ThreePorts G)
    (e f : E)
    (h : PairAgree (graphPort G p e false,graphPort G p e true)
      (graphPort G p f false,graphPort G p f true)) : e=f := by
  rcases h with (⟨h0,_⟩ | ⟨h0,_⟩)
  · exact congrArg Prod.fst (graphPort_inj G p (a₁ := (e,false)) (a₂ := (f,false)) h0)
  · exact congrArg Prod.fst (graphPort_inj G p (a₁ := (e,false)) (a₂ := (f,true)) h0)

private theorem no_same_detached {V : Type*} (a : V × Fin 5) (b : Variable V)
    (h : PairAgree (Sum.inl a,b) (Sum.inr false,Sum.inr true)) : False := by
  rcases h with (⟨h0,_⟩ | ⟨h0,_⟩) <;> exact Sum.noConfusion h0

private theorem agree_clause_indices {V E : Type*} (G : Graph V E) (p : ThreePorts G)
    (s : V → Bool) (hloop : ∀ e, G e false ≠ G e true) (i j : ClauseId V E)
    (h : PairAgree (pairOf G p s i) (pairOf G p s j)) : i=j := by
  rcases i with ((⟨v,i⟩ | v) | (e | ⟨⟩)) <;> rcases j with ((⟨w,j⟩ | w) | (f | ⟨⟩))
  · exact congrArg (fun x => Sum.inl (Sum.inl x)) (cycle_cycle G p s v w i j h)
  · exact False.elim (cycle_switch G p s v w i h)
  · exact False.elim (local_conflict G p hloop v f i (i+1) h)
  · exact False.elim (no_same_detached (v,i) _ h)
  · exact False.elim (cycle_switch G p s w v j h.symm)
  · have h' : PairAgree ((Sum.inl (v,(0 : Fin 5)) : Variable V),Sum.inl (v,2)) (Sum.inl (w,0),Sum.inl (w,2)) := h
    rcases h' with (⟨h0,_⟩ | ⟨h0,_⟩) <;>
      exact congrArg (fun x => Sum.inl (Sum.inr x)) (congrArg Prod.fst (Sum.inl.inj h0))
  · exact False.elim (local_conflict G p hloop v f 0 2 h)
  · exact False.elim (no_same_detached (v,0) _ h)
  · exact False.elim (local_conflict G p hloop w e j (j+1) h.symm)
  · exact False.elim (local_conflict G p hloop w e 0 2 h.symm)
  · exact congrArg (fun x => Sum.inr (Sum.inl x)) (conflict_conflict G p e f h)
  · exact False.elim (no_same_detached _ _ h)
  · exact False.elim (no_same_detached (w,j) _ h.symm)
  · exact False.elim (no_same_detached (w,0) _ h.symm)
  · exact False.elim (no_same_detached _ _ h.symm)
  · rfl

/-- The exact five-copy formula has no equal supports among different binary
clauses. It cannot gain a duplicate or a subsumption for any input signs. -/
theorem supports_injective {V E : Type*} [DecidableEq V]
    (G : Graph V E) (p : ThreePorts G) (s : V → Bool)
    (hloop : ∀ e, G e false ≠ G e true) : Function.Injective (support G p s) := by
  intro i j h
  have hn : (pairOf G p s i).1 ≠ (pairOf G p s i).2 := by
    intro he
    have hc := support_width G p s i
    change ({(pairOf G p s i).1,(pairOf G p s i).2} : Finset (Variable V)).card = 2 at hc
    rw [he] at hc
    simp at hc
  exact agree_clause_indices G p s hloop i j (agree_of_support_eq _ _ _ _ hn h)

theorem no_distinct_subsumptions {V E : Type*} [DecidableEq V]
    (G : Graph V E) (p : ThreePorts G) (s : V → Bool) (hloop : ∀ e, G e false ≠ G e true)
    (i j : ClauseId V E) (h : support G p s i ⊆ support G p s j) : i=j := by
  apply supports_injective G p s hloop
  apply Finset.eq_of_subset_of_card_le h
  rw [support_width,support_width]

#print axioms supports_injective
#print axioms no_distinct_subsumptions

end V8PooledRange
