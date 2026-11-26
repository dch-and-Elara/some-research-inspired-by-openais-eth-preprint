import P5MainIteratorSourceLayout
import P5MainIteratorTrace

/-! The full-cell cap alone does not entail the source's independent
variable-group balance. Five letters and arbitrarily many coordinates:
one incidence in each full cell, every unselected variable has degree
five, but one group contains five ninths of the variables. -/
namespace P5MainIterator.Unbalanced
open scoped BigOperators Classical

variable (I : Type*) [Fintype I]

abbrev A := I → Fin 5
abbrev Word := Fin 5 × A I
abbrev Vars := (A I × Word I) ⊕ ({b : Fin 5 // b ≠ 0} × A I × A I)
abbrev E := Word I × Word I
abbrev Cell := WordCell (Option I) (Fin 5)

def word (w : Word I) (t : Option I) : Fin 5 :=
  Option.elim t w.1 w.2

def ord (e : E I) (t : Option I) : Fin 5 × Fin 5 :=
  (word I e.1 t, word I e.2 t)

def ordEquiv : E I ≃ Cell I where
  toFun := ord I
  invFun u := (((u none).1,fun t => (u (some t)).1),((u none).2,fun t => (u (some t)).2))
  left_inv e := by cases e; rfl
  right_inv u := by
    funext t
    cases t <;> simp [ord,word]

def owner (e : E I) : Vars I :=
  if h : e.1.1=0 then Sum.inl (e.1.2,e.2)
    else Sum.inr (⟨e.1.1,h⟩,e.1.2,e.2.2)

def a (v : Vars I) : Option I → Fin 5 :=
  match v with
  | Sum.inl q => word I (0,q.1)
  | Sum.inr q => word I (q.1.val,q.2.1)

omit [Fintype I] in
theorem owner_surjective : Function.Surjective (owner I) := by
  rintro (⟨w,d⟩ | ⟨⟨g,hg⟩,w,d⟩)
  · exact ⟨((0,w),d),by simp [owner]⟩
  · exact ⟨((g,w),(0,d)),by simp [owner,hg]⟩

def layout : SourceLayout (E I) (Vars I) (Word I) (Fin 2) (Option I) (Fin 5) where
  placement := ⟨owner I, ⟨fun e => (0,ord I e),fun _ _ h => (ordEquiv I).injective (congrArg Prod.snd h)⟩,
    owner_surjective I⟩
  factor := Prod.snd
  a := a I
  d := word I
  first e t := by
    change word I e.1 t = a I (owner I e) t
    by_cases h : e.1.1=0
    · cases t <;> simp [owner,a,word,h]
    · simp [owner,a,h]
  second _ _ := rfl

theorem cellLoad_one (u : Cell I) : cellLoad (layout I) u=1 := by
  unfold cellLoad
  have h : (Finset.univ.filter fun e : E I => ((layout I).placement.slot e).2=u) =
      {(ordEquiv I).symm u} := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ((ordEquiv I).apply_eq_iff_eq_symm_apply)
  rw [h,Finset.card_singleton]

theorem exact_cap (u : Cell I) :
    cellLoad (layout I) u * Fintype.card (Cell I) ≤ 2*Fintype.card (E I) := by
  rw [cellLoad_one,one_mul,←Fintype.card_congr (ordEquiv I)]
  omega

def groupZeroEquiv : {v : Vars I // a I v none = 0} ≃ (A I × Word I) where
  toFun v := by
    rcases v with ⟨w,hw⟩
    cases w with
    | inl l => exact l
    | inr r => exact False.elim (r.1.property hw)
  invFun w := ⟨Sum.inl w,rfl⟩
  left_inv v := by
    rcases v with ⟨w,hw⟩
    cases w with
    | inl l => rfl
    | inr r => exact False.elim (r.1.property hw)
  right_inv _ := rfl

theorem card_vars : Fintype.card (Vars I) = 9*(Fintype.card (A I))^2 := by
  have h : Fintype.card {b : Fin 5 // b ≠ (0:Fin 5)}=4 := by decide
  unfold Vars Word
  rw [Fintype.card_sum,Fintype.card_prod,Fintype.card_prod,Fintype.card_prod,Fintype.card_prod,h,Fintype.card_fin]
  ring

theorem group_zero_card : Fintype.card {v : Vars I // a I v none = 0}
    = 5*(Fintype.card (A I))^2 := by
  rw [Fintype.card_congr (groupZeroEquiv I)]
  unfold Word
  rw [Fintype.card_prod,Fintype.card_prod,Fintype.card_fin]
  ring

/-- More than the purported independent group bound 2n/r. The uniform
cell-cap hypothesis and source incidence representation both hold. -/
theorem cap_does_not_imply_balance :
    2*Fintype.card (Vars I) <
      5*Fintype.card {v : Vars I // (layout I).a v none=0} := by
  change 2*Fintype.card (Vars I) < 5*Fintype.card {v : Vars I // a I v none=0}
  rw [card_vars,group_zero_card]
  have h : 0<Fintype.card (A I) := Fintype.card_pos_iff.mpr ⟨fun _=>0⟩
  nlinarith

#print axioms owner_surjective
#print axioms cellLoad_one
#print axioms exact_cap
#print axioms card_vars
#print axioms group_zero_card
#print axioms cap_does_not_imply_balance
end P5MainIterator.Unbalanced
