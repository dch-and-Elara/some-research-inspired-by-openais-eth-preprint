import P5HybridClosureActual

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000
set_option linter.unusedSectionVars false

/-! Only actual pinned unary clause factors use the new tags.
Interior triples and exterior mates keep the same source pin incidence. -/
namespace Paper5.HybridMainOnly
open scoped Classical BigOperators
open Paper5.HybridClosure J1MainSourceCollision

noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (E : Finset (V×V)) (cubic : ∀ v,GraphCutMoments.degree E v=3)
local notation "F" => (replacedEdges E cubic)
local notation "Port" => (MainClonedCNF.Port F)

def mateTag : ClauseIndex F→Option E
  | .inl p => some ((exteriorPort E cubic).symm p).1
  | .inr _ => none

theorem mate_tied_slots :
    (tiedSlots (mateTag E cubic ∘ cloneFactor F)).card=Fintype.card (TriVertex V) := by
  have h : tiedSlots (mateTag E cubic ∘ cloneFactor F)=
      Finset.univ.map (MainClonedCNF.pinPort F) := by
    ext x
    rcases x with x|x
    · simp [tiedSlots,mateTag,MainClonedCNF.pinPort,cloneFactor]
    · rcases x with x|x <;> simp [tiedSlots,mateTag,MainClonedCNF.pinPort,cloneFactor]
  rw [h,Finset.card_map,Finset.card_univ]

/-- The exterior tag fibre consists of exactly the two physical pin
incidences of this real matching edge. -/
theorem mate_tied_fibre (e : E) :
    (tagFibre (mateTag E cubic ∘ cloneFactor F) e).card=2 := by
  let j : Bool↪Port :=
    ⟨fun b=>.inl (exteriorPort E cubic (e,b)), fun _ _ h=>
      congrArg Prod.snd ((exteriorPort E cubic).injective (Sum.inl.inj h))⟩
  have h : tagFibre (mateTag E cubic ∘ cloneFactor F) e=Finset.univ.map j := by
    ext x
    rcases x with p|p
    · constructor
      · intro hp
        have ht : ((exteriorPort E cubic).symm p).1=e := by
          simpa [tagFibre,mateTag,cloneFactor] using hp
        have hi : (e,((exteriorPort E cubic).symm p).2)=(exteriorPort E cubic).symm p :=
          Prod.ext ht.symm rfl
        refine Finset.mem_map.mpr ⟨((exteriorPort E cubic).symm p).2,Finset.mem_univ _,?_⟩
        change Sum.inl (exteriorPort E cubic (e,((exteriorPort E cubic).symm p).2))=Sum.inl p
        rw [hi,Equiv.apply_symm_apply]
      · intro hp
        obtain ⟨b,_,hb⟩ := Finset.mem_map.mp hp
        change Sum.inl (exteriorPort E cubic (e,b))=Sum.inl p at hb
        have he := Sum.inl.inj hb
        subst p
        simp [tagFibre,mateTag,cloneFactor]
    · rcases p with p|p <;> simp [tagFibre,mateTag,cloneFactor,j]
  rw [h,Finset.card_map,Finset.card_univ,Fintype.card_bool]

variable {I : Type*} [DecidableEq I]

def literalTags (t u : I) (j : I) (c : ClauseIndex F) : Option (V⊕E) :=
  if j=t then (triangleTie c).map Sum.inl
  else if j=u then (mateTag E cubic c).map Sum.inr else none

theorem literal_tags_first (t u : I) (p : TriVertex V) :
    literalTags E cubic t u t (.inl p)=some (.inl p.1) := by
  simp [literalTags,triangleTie]

theorem literal_tags_second (t u : I) (ne : t≠u) (p : TriVertex V) :
    literalTags E cubic t u u (.inl p)=some (.inr ((exteriorPort E cubic).symm p).1) := by
  simp [literalTags,mateTag,Ne.symm ne]

theorem literal_tri_mates_separate (ne : ∀ v,(v,v)∉E) (e : E) :
    (exteriorPort E cubic (e,false)).1 ≠ (exteriorPort E cubic (e,true)).1 := by
  rw [exteriorPort_left_base,exteriorPort_right_base]
  intro eq
  have he : (e.val.1,e.val.2)∈E := e.property
  exact ne e.val.1 (by simpa [←eq] using he)

#print axioms mate_tied_slots
#print axioms mate_tied_fibre
#print axioms literal_tags_first
#print axioms literal_tags_second
#print axioms literal_tri_mates_separate
end
end Paper5.HybridMainOnly