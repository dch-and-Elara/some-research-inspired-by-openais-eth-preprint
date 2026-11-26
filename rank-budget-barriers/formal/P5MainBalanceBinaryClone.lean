import P5MainBalanceTerminal
import MainClonedCNF
import Mathlib.Tactic.FinCases

/-! A two-coordinate, two-symbol scope chart for every true cubic clone.
The cell cap and variable balance hold, but all marked pins belong to
one factor-sign group. This is not the published r growing with n. -/
namespace P5MainBalance.BinaryClone
open scoped BigOperators Classical
open P5MainIterator

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : Finset (V×V)) (regular : ∀ v,GraphCutMoments.degree G v=3)

abbrev CopyVar (V : Type*) := V×Fin 4
abbrev Uses (V : Type*) := V×Fin 4×Fin 3
abbrev Factor := V ⊕ (G ⊕ (V×Fin 4))

def firstWord (i : Fin 4) (t : Fin 2) : Fin 2 :=
  if t=0 then ⟨i.val/2,by omega⟩ else ⟨i.val%2,by omega⟩

theorem firstWord_inj : Function.Injective firstWord := by
  intro i j h
  have h0 := congrArg Fin.val (congrFun h (0:Fin 2))
  have h1 := congrArg Fin.val (congrFun h (1:Fin 2))
  change i.val/2=j.val/2 at h0
  change i.val%2=j.val%2 at h1
  apply Fin.ext
  omega

def cycleD (i : Fin 4) (t : Fin 2) : Fin 2 :=
  if ((i.val%2 == 0) == (t.val==0)) then 0 else 1

def localD (i : Fin 4) (j : Fin 3) (t : Fin 2) : Fin 2 :=
  if j=0 then (if i.val=0 then 0 else 1)
  else if j=1 then cycleD i t else cycleD (i-1) t

private theorem three_words_fixed_table :
    ∀ (i : Fin 4) (j k : Fin 3), (∀ t : Fin 2,localD i j t=localD i k t) → j=k := by decide

def factorD (f : Factor G) (t : Fin 2) : Fin 2 :=
  match f with
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr (_,i)) =>
    cycleD i t

noncomputable def externalFactor (v : V) (i : Fin 4) : Factor G :=
  if h:i.val=0 then Sum.inl v else
    match (MainClonedCNF.edgeNumber G regular v).symm ⟨i.val-1,by omega⟩ with
    | Sum.inl e => Sum.inr (Sum.inl ⟨e.val,(Finset.mem_filter.mp e.property).1⟩)
    | Sum.inr e => Sum.inr (Sum.inl ⟨e.val,(Finset.mem_filter.mp e.property).1⟩)

noncomputable def factor (e : Uses V) : Factor G :=
  if e.2.2=0 then externalFactor G regular e.1 e.2.1
  else if e.2.2=1 then Sum.inr (Sum.inr (e.1,e.2.1))
  else Sum.inr (Sum.inr (e.1,e.2.1-1))

omit [Fintype V] in
theorem external_word (v : V) (i : Fin 4) (t : Fin 2) :
    factorD G (externalFactor G regular v i) t = if i.val=0 then 0 else 1 := by
  unfold externalFactor
  split
  · rfl
  · split <;> rfl

omit [Fintype V] in
theorem own_three_factor_words (v : V) (i : Fin 4) :
    Function.Injective (fun j : Fin 3 => factorD G (factor G regular (v,i,j))) := by
  intro j k h
  apply three_words_fixed_table i j k
  intro t
  have H (u : Fin 3) :
      factorD G (factor G regular (v,i,u)) t = localD i u t := by
    unfold factor localD
    by_cases hu : u=0
    · rw [if_pos hu,if_pos hu,external_word]
    · rw [if_neg hu,if_neg hu]
      by_cases hv : u=1
      · rw [if_pos hv,if_pos hv]; rfl
      · rw [if_neg hv,if_neg hv]; rfl
  exact (H j).symm.trans ((congrFun h t).trans (H k))

def mark : V ↪ Uses V := ⟨fun v => (v,0,0),fun _ _ h=>congrArg Prod.fst h⟩

noncomputable def chart :
    SourceLayout (Uses V) (CopyVar V) (Factor G) V (Fin 2) (Fin 2) where
  placement :=
    { owner := fun e => (e.1,e.2.1)
      occurs := fun v => ⟨(v.1,v.2,0),rfl⟩
      slot :=
        { toFun := fun e=> (e.1,fun t=>(firstWord e.2.1 t,factorD G (factor G regular e) t))
          inj' := by
            rintro ⟨v,i,j⟩ ⟨w,a,b⟩ h
            have hf : v=w := congrArg Prod.fst h
            subst w
            have hi : i=a := firstWord_inj (funext fun t => congrArg (fun z : V×WordCell (Fin 2) (Fin 2) => (z.2 t).1) h)
            subst a
            have hj : j=b := own_three_factor_words G regular v i (funext fun t =>
              congrArg (fun z : V×WordCell (Fin 2) (Fin 2) => (z.2 t).2) h)
            subst b
            rfl } }
  factor := factor G regular
  a := fun v=>firstWord v.2
  d := factorD G
  first _ _ := rfl
  second _ _ := rfl

omit [Fintype V] in
theorem pin_word_constant (v : V) (t : Fin 2) :
    pinWord (chart G regular) (mark (V:=V)) v t=0 := by
  change factorD G (factor G regular (v,0,0)) t=0
  simp [factor,external_word]

theorem binary_cell_cap (u : WordCell (Fin 2) (Fin 2)) :
    cellLoad (chart G regular) u * Fintype.card (WordCell (Fin 2) (Fin 2))≤
      2*Fintype.card (Uses V) := by
  let S := Finset.univ.filter (fun e : Uses V => ((chart G regular).placement.slot e).2=u)
  have hi : Function.Injective (fun e : S => e.val.1) := by
    intro e f he
    apply Subtype.ext
    apply (chart G regular).placement.slot.injective
    have h₁ : ((chart G regular).placement.slot e.val).1=((chart G regular).placement.slot f.val).1 := he
    have hue := (Finset.mem_filter.mp e.property).2
    have huf := (Finset.mem_filter.mp f.property).2
    exact Prod.ext h₁ (hue.trans huf.symm)
  have h := Fintype.card_le_of_injective _ hi
  simp only [Fintype.card_coe] at h
  have hD : Fintype.card (WordCell (Fin 2) (Fin 2))=16 := by
    change Fintype.card (Fin 2→Fin 2×Fin 2)=16
    norm_num [Fintype.card_fun,Fintype.card_prod]
  have hM : Fintype.card (Uses V)=12*Fintype.card V := by simp [Uses]; omega
  rw [hD,hM]
  change S.card*16≤_
  omega

theorem binary_groups_balance (t a : Fin 2) :
    Fintype.card {v : CopyVar V // (chart G regular).a v t=a} * 2 ≤
      2*Fintype.card (CopyVar V) :=
  by simpa only [Nat.mul_comm] using Nat.mul_le_mul_right 2 (Fintype.card_subtype_le (fun v : CopyVar V => (chart G regular).a v t=a))

omit [Fintype V] in
theorem binary_one_group_exact (F : (V→Bool)→ℚ) (σ : V→Bool) :
    (collapsedOnlyGroup (pinWord (chart G regular) (mark (V:=V))) 0 0
      (fun v => pin_word_constant G regular v 0) F).value σ=F σ :=
  collapsed_group_represents_everything _ 0 0 _ F σ

#print axioms own_three_factor_words
#print axioms pin_word_constant
#print axioms binary_cell_cap
#print axioms binary_groups_balance
#print axioms binary_one_group_exact
end P5MainBalance.BinaryClone
