import S8Placement

namespace S8

set_option maxHeartbeats 1200000

open SourceDensity GraphCutMoments

variable {V : Type*} [Fintype V] [DecidableEq V]

def clauseTag (E : Finset (V × V)) : MainClonedCNF.Port E → Bool
  | .inl _ => false
  | .inr (.inl (_,b)) => b
  | .inr (.inr (_,_,b)) => b

def cloneTag (E : Finset (V × V)) : MainClonedCNF.Port E → Fin 3
  | .inr (.inr (_,_,false)) => 1
  | .inr (.inr (_,_,true)) => 2
  | _ => 0

theorem clauseDegree (E : Finset (V × V)) (x : Clause E) :
    fiberCount (portClause E) x ≤ 2 := by
  classical
  unfold fiberCount
  rw [← Fintype.card_bool, ← Finset.card_univ]
  apply Finset.card_le_card_of_injOn (clauseTag E)
  · exact fun _ _ => Finset.mem_univ _
  · intro e he f hf h
    have heq := (Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm
    rcases e with (v | (⟨p,b⟩ | ⟨v,i,b⟩)) <;>
      rcases f with (w | (⟨q,c⟩ | ⟨w,j,c⟩)) <;> simp only [portClause, clauseTag, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq,
        reduceCtorEq] at heq h ⊢ <;> tauto

theorem cloneDegree (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) (x : V × Fin 4) :
    fiberCount (portClone E reg) x ≤ 3 := by
  classical
  unfold fiberCount
  rw [← Fintype.card_fin 3, ← Finset.card_univ]
  apply Finset.card_le_card_of_injOn (cloneTag E)
  · exact fun _ _ => Finset.mem_univ _
  · intro e he f hf h
    have heq := (Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm
    clear he hf
    rcases e with (v | (⟨⟨⟨u,v⟩,huv⟩,b⟩ | ⟨v,i,b⟩)) <;>
      rcases f with (w | (⟨⟨⟨x,y⟩,hxy⟩,c⟩ | ⟨w,j,c⟩))
    all_goals try cases b
    all_goals try cases c
    all_goals
      simp only [cloneTag, portClone, Bool.false_eq_true, if_false, if_true,
        Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, MainClonedCNF.leftSlot,
        MainClonedCNF.rightSlot, Fin.succ_inj] at *
    all_goals try (solve | simp_all | omega)
    all_goals
      obtain ⟨hh, hh'⟩ := heq
      first
      | exact (Fin.succ_ne_zero _ hh').elim
      | exact (Fin.succ_ne_zero _ hh'.symm).elim
      | subst_vars
        have hslot := (MainClonedCNF.edgeNumber E reg _).injective hh'
        simp at hslot ⊢ <;> exact hslot

theorem wireOldDegree (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) (x : OldVertex E) :
    fiberCount (wireOld E reg) x ≤ 3 := by
  classical
  cases x with
  | inl x =>
    refine le_trans ?_ (cloneDegree E reg x)
    unfold fiberCount
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro ⟨p,b⟩ h
      cases b <;> simpa [wireOld] using h
    · intro ⟨p,b⟩ hp ⟨q,c⟩ hq h
      cases b <;> cases c <;>
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, wireOld, Bool.false_eq_true,
          if_false, if_true, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Prod.mk.injEq] at hp hq h ⊢ <;>
        tauto
  | inr x =>
    refine le_trans ?_ ((clauseDegree E x).trans (by decide))
    unfold fiberCount
    apply Finset.card_le_card_of_injOn Prod.fst
    · intro ⟨p,b⟩ h
      cases b <;> simpa [wireOld] using h
    · intro ⟨p,b⟩ hp ⟨q,c⟩ hq h
      cases b <;> cases c <;>
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and, wireOld, Bool.false_eq_true,
          if_false, if_true, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, Prod.mk.injEq] at hp hq h ⊢ <;>
        tauto

theorem subdivDegree (E : Finset (V × V)) (p : MainClonedCNF.Port E) :
    fiberCount (fun w : Wire E => w.1) p ≤ 2 := by
  classical
  unfold fiberCount
  rw [← Fintype.card_bool, ← Finset.card_univ]
  apply Finset.card_le_card_of_injOn Prod.snd
  · exact fun _ _ => Finset.mem_univ _
  · intro ⟨q,b⟩ hq ⟨r,c⟩ hr h
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hq hr
    exact Prod.ext (hq.trans hr.symm) h

#print axioms clauseDegree
#print axioms cloneDegree
#print axioms wireOldDegree
#print axioms subdivDegree

end S8

