import P5HybridClosurePorts
import J6R11CollisionReindex

/-! The physical D root graph of the very same cloned CNF. Each of its
literal incidences is subdivided once. The two physical wires carry a Bool
tag distinguishing the assignment-side and clause-side halves. -/
namespace Paper5.HybridClosure
open scoped BigOperators Classical
open J1MainSourceCollision
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]

abbrev DWire (F : Finset (W×W)) := MainClonedCNF.Port F × Bool
abbrev DOld (F : Finset (W×W)) := Clone W ⊕ ClauseIndex F

noncomputable def dNetwork (F : Finset (W×W)) (cubic : ∀v,GraphCutMoments.degree F v=3) :
    J6R10Repack.Network (DWire F) (DOld F) (MainClonedCNF.Port F) where
  row p := if p.2 then .inr (cloneFactor F p.1) else .inl (cloneOwner F cubic p.1)
  col p := p.1

theorem d_physical_wire_count (F : Finset (W×W)) (cubic : ∀v,GraphCutMoments.degree F v=3) :
    Fintype.card (DWire F)=24*Fintype.card W := by
  rw [Fintype.card_prod,Fintype.card_bool,MainClonedCNF.port_card F cubic]
  omega

theorem d_subdivision_degree (F : Finset (W×W)) (cubic : ∀v,GraphCutMoments.degree F v=3)
    (p : MainClonedCNF.Port F) :
    (varFibre (dNetwork F cubic).col p).card=2 := by
  let e : Bool ↪ DWire F := ⟨fun b => (p,b),fun _ _ h => congrArg Prod.snd h⟩
  have he : varFibre (dNetwork F cubic).col p=Finset.univ.map e := by
    ext x
    rcases x with ⟨q,b⟩
    cases b <;> simp [varFibre,dNetwork,e]
  rw [he,Finset.card_map,Finset.card_univ,Fintype.card_bool]

omit [Fintype W] [DecidableEq W] in
private theorem inject_wire_inl (F : Finset (W×W)) :
    Function.Injective (fun p : MainClonedCNF.Port F => (p,false)) :=
  fun _ _ h => congrArg Prod.fst h

omit [Fintype W] [DecidableEq W] in
private theorem inject_wire_inr (F : Finset (W×W)) :
    Function.Injective (fun p : MainClonedCNF.Port F => (p,true)) :=
  fun _ _ h => congrArg Prod.fst h

theorem d_old_degree (F : Finset (W×W)) (cubic : ∀v,GraphCutMoments.degree F v=3)
    (p : DOld F) : (facFibre (dNetwork F cubic).row p).card≤3 := by
  rcases p with p|p
  · let e : MainClonedCNF.Port F ↪ DWire F := ⟨_,inject_wire_inl F⟩
    have he : facFibre (dNetwork F cubic).row (.inl p) =
        (varFibre (cloneOwner F cubic) p).map e := by
      ext x
      rcases x with ⟨x,b⟩
      cases b
      · simp [facFibre,varFibre,dNetwork,e]
      · simp [facFibre,dNetwork,e]
    rw [he,Finset.card_map,every_clone_three]
  · let e : MainClonedCNF.Port F ↪ DWire F := ⟨_,inject_wire_inr F⟩
    have he : facFibre (dNetwork F cubic).row (.inr p) =
        (facFibre (cloneFactor F) p).map e := by
      ext x
      rcases x with ⟨x,b⟩
      cases b
      · simp [facFibre,dNetwork,e]
      · simp [facFibre,dNetwork,e]
    rw [he,Finset.card_map]
    exact (every_clause_at_most_two F p).trans (by decide)

section TiedPhysical
variable (E : Finset (V×V)) (cubic : ∀v,GraphCutMoments.degree E v=3)
variable (loopless : ∀v,(v,v)∉E)

local notation "F" => replacedEdges E cubic
local notation "reg" => replaced_cubic E cubic loopless

noncomputable def exteriorTie : DOld F→Option E
  | .inr (.inl p) => some ((exteriorPort E cubic).symm p).1
  | _ => none

noncomputable def pinWire (p : TriVertex V) : DWire F :=
  (.inl p,true)

theorem pinWire_injective : Function.Injective (pinWire E cubic) := by
  intro p q h
  exact Sum.inl.inj (congrArg Prod.fst h)

theorem d_unary_tag (p : TriVertex V) :
    exteriorTie E cubic ((dNetwork F reg).row (pinWire E cubic p)) =
      some ((exteriorPort E cubic).symm p).1 := rfl

theorem d_tied_slots :
    (tiedSlots (exteriorTie E cubic ∘ (dNetwork F reg).row)).card=Fintype.card (TriVertex V) := by
  let ι : TriVertex V ↪ DWire F := ⟨_,pinWire_injective E cubic⟩
  have h : tiedSlots (exteriorTie E cubic ∘ (dNetwork F reg).row)=Finset.univ.map ι := by
    ext p
    rcases p with ⟨p,b⟩
    cases b
    · simp [tiedSlots,exteriorTie,dNetwork,ι,pinWire]
    · rcases p with p|q
      · simp [tiedSlots,exteriorTie,dNetwork,cloneFactor,ι,pinWire]
      · rcases q with q|q <;> simp [tiedSlots,exteriorTie,dNetwork,cloneFactor,ι,pinWire]
  rw [h,Finset.card_map,Finset.card_univ]

theorem d_tied_fibre (x : E) :
    (tagFibre (exteriorTie E cubic ∘ (dNetwork F reg).row) x).card≤2 := by
  let f := fun p : (tagFibre (exteriorTie E cubic ∘ (dNetwork F reg).row) x) =>
    match p.val.1 with
    | .inl q => ((exteriorPort E cubic).symm q).2
    | .inr _ => false
  have hf : Function.Injective f := by
    intro p q h
    obtain ⟨⟨p,b⟩,hp⟩ := p
    obtain ⟨⟨q,c⟩,hq⟩ := q
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    cases b
    · simp [exteriorTie,dNetwork] at hp'
    cases c
    · simp [exteriorTie,dNetwork] at hq'
    rcases p with p|pp
    · rcases q with q|qq
      · have h₁ : ((exteriorPort E cubic).symm p).1=x := Option.some.inj hp'
        have h₂ : ((exteriorPort E cubic).symm q).1=x := Option.some.inj hq'
        have hzero : p=q := (exteriorPort E cubic).symm.injective
          (Prod.ext (h₁.trans h₂.symm) h)
        subst q
        rfl
      · rcases qq with qq|qq <;> simp [exteriorTie,dNetwork,cloneFactor] at hq'
    · rcases pp with pp|pp <;> simp [exteriorTie,dNetwork,cloneFactor] at hp'
  simpa only [Fintype.card_coe,Fintype.card_bool] using Fintype.card_le_of_injective f hf
end TiedPhysical

#print axioms dNetwork
#print axioms d_physical_wire_count
#print axioms d_subdivision_degree
#print axioms d_old_degree
#print axioms d_unary_tag
#print axioms d_tied_slots
#print axioms d_tied_fibre
end Paper5.HybridClosure