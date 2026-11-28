import P5HybridClosureGraph
import P5HybridClosureProduct
import J1MainSourceCollision

/-! Graph-only, literal incidence maps for a canonical cloned CNF. Pins
use clone 0, three incident edge literals use clones 1,2,3, and each clone
has the other two literal occurrences on its two cycle neighbors. -/
namespace Paper5.HybridClosure
open scoped BigOperators Classical
variable {W : Type*} [Fintype W] [DecidableEq W]

abbrev Clone (W : Type*) := W × Fin 4

abbrev ClauseIndex (E : Finset (W×W)) := W ⊕ (E ⊕ Clone W)

noncomputable def nonCycleOwner (E : Finset (W×W)) (cubic : ∀v,GraphCutMoments.degree E v=3) :
    W ⊕ (E×Bool) ≃ Clone W where
  toFun
    | .inl v => (v,0)
    | .inr p => ((exteriorPort E cubic p).1,(exteriorPort E cubic p).2.succ)
  invFun p := Fin.cases (.inl p.1) (fun i => .inr ((exteriorPort E cubic).symm (p.1,i))) p.2
  left_inv := by
    intro p
    cases p <;> simp
  right_inv := by
    rintro ⟨v,i⟩
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

def cycleSlot (p : W×Fin 4×Bool) : Clone W × Bool :=
  ((p.1, if p.2.2 then p.2.1+1 else p.2.1),p.2.2)

def cycleSlotInv (p : Clone W × Bool) : W×Fin 4×Bool :=
  (p.1.1,if p.2 then p.1.2-1 else p.1.2,p.2)

def cycleEquiv : (W×Fin 4×Bool) ≃ Clone W × Bool where
  toFun := cycleSlot
  invFun := cycleSlotInv
  left_inv := by
    rintro ⟨v,i,b⟩
    cases b <;> simp [cycleSlot,cycleSlotInv]
  right_inv := by
    rintro ⟨⟨v,i⟩,b⟩
    cases b <;> simp [cycleSlot,cycleSlotInv]

noncomputable def occChart (E : Finset (W×W)) (cubic : ∀v,GraphCutMoments.degree E v=3) :
    MainClonedCNF.Port E ≃ Clone W × (Unit⊕Bool) :=
  (Equiv.sumAssoc W (E×Bool) (W×Fin 4×Bool)).symm.trans
    ((Equiv.sumCongr ((nonCycleOwner E cubic).trans (Equiv.prodPUnit _).symm)
      cycleEquiv).trans (Equiv.prodSumDistrib _ _ _).symm)

noncomputable def cloneOwner (E : Finset (W×W)) (cubic : ∀v,GraphCutMoments.degree E v=3)
    (p : MainClonedCNF.Port E) : Clone W := (occChart E cubic p).1

def cloneFactor (E : Finset (W×W)) : MainClonedCNF.Port E → ClauseIndex E
  | .inl v => .inl v
  | .inr (.inl p) => .inr (.inl p.1)
  | .inr (.inr (v,i,_)) => .inr (.inr (v,i))

omit [Fintype W] in
/-- Every canonical one of the four literal slots per base vertex is exactly
the appropriate variable of the cloned clause list. -/
theorem edge_owner_left (E : Finset (W×W)) (cubic : ∀v,GraphCutMoments.degree E v=3) (e : E) :
    cloneOwner E cubic (.inr (.inl (e,false))) = (e.1.1,MainClonedCNF.leftSlot E cubic e) := rfl

omit [Fintype W] in
theorem edge_owner_right (E : Finset (W×W)) (cubic : ∀v,GraphCutMoments.degree E v=3) (e : E) :
    cloneOwner E cubic (.inr (.inl (e,true))) = (e.1.2,MainClonedCNF.rightSlot E cubic e) := rfl

theorem every_clone_three (E : Finset (W×W)) (cubic : ∀v,GraphCutMoments.degree E v=3) (v : Clone W) :
    (J1MainSourceCollision.varFibre (cloneOwner E cubic) v).card = 3 := by
  let e : (J1MainSourceCollision.varFibre (cloneOwner E cubic) v) ≃ Unit⊕Bool :=
    { toFun := fun p => (occChart E cubic p.1).2
      invFun := fun i => ⟨(occChart E cubic).symm (v,i),Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,congrArg Prod.fst ((occChart E cubic).apply_symm_apply (v,i))⟩⟩
      left_inv := by
        intro p
        apply Subtype.ext
        apply (occChart E cubic).injective
        rw [Equiv.apply_symm_apply]
        exact Prod.ext ((Finset.mem_filter.mp p.property).2.symm) rfl
      right_inv := by
        intro i
        exact congrArg Prod.snd ((occChart E cubic).apply_symm_apply (v,i)) }
  have hc := Fintype.card_congr e
  simpa only [Fintype.card_sum,Fintype.card_unit,Fintype.card_bool,Fintype.card_coe] using hc

def clauseSide (E : Finset (W×W)) : MainClonedCNF.Port E → Bool
  | .inl _ => false
  | .inr (.inl p) => p.2
  | .inr (.inr p) => p.2.2

omit [Fintype W] [DecidableEq W] in
theorem clause_and_side_injective (E : Finset (W×W)) :
    Function.Injective (fun p : MainClonedCNF.Port E => (cloneFactor E p,clauseSide E p)) := by
  rintro (v|p) (w|q) he
  · simpa [cloneFactor,clauseSide] using he
  · rcases q with ⟨q,b⟩|⟨v,i,b⟩ <;> simp [cloneFactor] at he
  · rcases p with ⟨p,b⟩|⟨v,i,b⟩ <;> simp [cloneFactor] at he
  · rcases p with ⟨p,b⟩|⟨v,i,b⟩ <;> rcases q with ⟨q,c⟩|⟨w,j,c⟩ <;>
      simp [cloneFactor,clauseSide] at he ⊢
    · exact he
    · exact ⟨he.1.1,he.1.2,he.2⟩

theorem every_clause_at_most_two (E : Finset (W×W)) (f : ClauseIndex E) :
    (J1MainSourceCollision.facFibre (cloneFactor E) f).card ≤ 2 := by
  let φ : (J1MainSourceCollision.facFibre (cloneFactor E) f)→Bool := fun p => clauseSide E p
  have hi : Function.Injective φ := by
    intro p q h
    apply Subtype.ext
    exact clause_and_side_injective E (Prod.ext ((Finset.mem_filter.mp p.property).2.trans ((Finset.mem_filter.mp q.property).2.symm)) h)
  have hc := Fintype.card_le_of_injective φ hi
  simpa only [Fintype.card_bool,Fintype.card_coe] using hc

#print axioms nonCycleOwner
#print axioms occChart
#print axioms edge_owner_left
#print axioms edge_owner_right
#print axioms every_clone_three
#print axioms every_clause_at_most_two
end Paper5.HybridClosure