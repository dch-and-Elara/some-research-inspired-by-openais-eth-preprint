import J1MainSourceBridge
import J1R14QueryFibre

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4300000
set_option linter.unusedSectionVars false

/-! Actual public copy addresses, before any sign or private-point read.
The arbitrary source tie-break is replaced by a fully specified stable
rank within each physical cell. An explicit lookup implements occupancy. -/
namespace J1R43Literal
open scoped BigOperators
open MainProbe J1MainSourcePlacement J1MainSourceBridge

section Copies
variable {I S E V F A : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
  [Fintype E] [DecidableEq E]
variable (D : IncidenceData I S E V F) (order : E ↪ ℕ)

def roster (c : Cell I S) : Finset E :=
  Finset.univ.filter (fun e => D.cell e=c)

def before (e : E) : Finset E :=
  (roster D (D.cell e)).filter (fun p => order p<order e)

def stableCopies : ℕ :=
  Finset.univ.sup (fun c : Cell I S => (roster D c).card)

theorem stableCopies_eq : stableCopies D=copies D := by
  unfold stableCopies copies
  congr 1
  funext c
  rw [fibre_eq_load D c]
  congr 1
  ext e
  simp [roster]

theorem before_lt (e : E) : (before D order e).card<stableCopies D := by
  have he : e ∈ roster D (D.cell e) := by simp [roster]
  have hn : e ∉ before D order e := by simp [before]
  have hr : before D order e ⊂ roster D (D.cell e) :=
    (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).2 ⟨e,he,hn⟩
  exact (Finset.card_lt_card hr).trans_le (Finset.le_sup
    (f:=fun c : Cell I S => (roster D c).card) (Finset.mem_univ _))

def stablePlace (e : E) : Fin (stableCopies D) × Cell I S :=
  (⟨(before D order e).card,before_lt D order e⟩,D.cell e)

theorem before_strict (e f : E) (hc : D.cell e=D.cell f) (h : order e<order f) :
    before D order e ⊂ before D order f := by
  have hsub : before D order e ⊆ before D order f := by
    intro x hx
    have hx := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hc ▸ hx.1,hx.2.trans h⟩
  apply (Finset.ssubset_iff_of_subset hsub).2
  refine ⟨e, Finset.mem_filter.mpr ⟨?_,h⟩,by simp [before]⟩
  simp [roster,hc]

theorem stablePlace_injective : Function.Injective (stablePlace D order) := by
  intro e f eq
  by_contra h
  have hd : order e ≠ order f := fun he => h (order.injective he)
  have hc : D.cell e=D.cell f := congrArg Prod.snd eq
  have hidx : (before D order e).card=(before D order f).card :=
    congrArg (fun p => p.1.val) eq
  rcases lt_or_gt_of_ne hd with he|hf
  · exact (Finset.card_lt_card (before_strict D order e f hc he)).ne hidx
  · exact (Finset.card_lt_card (before_strict D order f e hc.symm hf)).ne hidx.symm

end Copies

section Lookup
variable {E C : Type*} [DecidableEq C]

def findSlot (key : E → C) (value : C) : List E → Option E
  | [] => none
  | e::es => if key e=value then some e else findSlot key value es

theorem findSlot_at (key : E → C) (hinj : Function.Injective key)
    (es : List E) (e : E) (he : e∈es) :
    findSlot key (key e) es=some e := by
  induction es with
  | nil => simp at he
  | cons a as ih =>
    by_cases h : key a=key e
    · simpa [findSlot,h] using congrArg some (hinj h)
    · have tha : a≠e := fun hh => h (congrArg key hh)
      exact (if_neg h).trans (ih ((List.mem_cons.mp he).resolve_left (Ne.symm tha)))

theorem findSlot_empty (key : E → C) (value : C) (es : List E)
    (miss : ∀ e ∈ es,key e≠value) :
    findSlot key value es=none := by
  induction es with
  | nil => rfl
  | cons a as ih =>
    simp only [findSlot, if_neg (miss a (List.mem_cons_self ..))]
    exact ih (fun e he => miss e (List.mem_cons_of_mem _ he))

end Lookup

section Export
variable {I S E V F A : Type*} [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
  [Fintype E] [DecidableEq E]
variable (D : IncidenceData I S E V F) (order : E ↪ ℕ) (ports : List E)
  (all : ∀ e, e∈ports) (pin : A → E)

def stableOccupied (c : Fin (stableCopies D)) (u : Cell I S) : Option V :=
  (findSlot (stablePlace D order) (c,u) ports).map D.var

def stableLayout : DiagonalLayout I S V (Fin (stableCopies D)) (Diagonal D pin) where
  occupied := stableOccupied D order ports
  variableWord := D.wordVar
  slot := fun p => D.cell (pin p.val)
  copy := fun p => (stablePlace D order (pin p.val)).1
  pinVar := fun p => D.var (pin p.val)
  localSlot := by
    intro p
    unfold stableOccupied
    change (findSlot (stablePlace D order) (stablePlace D order (pin p.val)) ports).map D.var=_
    rw [findSlot_at _ (stablePlace_injective D order) _ _ (all _)]
    rfl
  variableLabel := fun _ => rfl
  diagonal := fun p => p.property

variable [Fintype A] [DecidableEq A]

theorem owned_stable_equals_hits (i : I) (g : S) :
    (ownedPins (stableLayout D order ports all pin) i g Finset.univ).card =
      (hits D pin i g).card := by
  let group := ownedPins (stableLayout D order ports all pin) i g Finset.univ
  have groupDef (a : Diagonal D pin) :
      a ∈ group ↔ (D.cell (pin a.val)).2 i = g := by
    simp [group,ownedPins,stableLayout]
  let cast : ↥group ≃ ↥(hits D pin i g) :=
    { toFun a := ⟨a.val.val,(mem_hits D pin i g _).mpr ⟨a.val.property,(groupDef a.val).mp a.property⟩⟩
      invFun a := ⟨⟨a.val,((mem_hits D pin i g _).mp a.property).1⟩,
        (groupDef _).mpr ((mem_hits D pin i g _).mp a.property).2⟩
      left_inv a := by rfl
      right_inv a := by rfl }
  exact (Fintype.card_coe group).symm.trans
    ((Fintype.card_congr cast).trans (Fintype.card_coe _))

end Export

#print axioms stableCopies_eq
#print axioms before_lt
#print axioms before_strict
#print axioms stablePlace_injective
#print axioms findSlot_at
#print axioms findSlot_empty
#print axioms stableLayout
#print axioms owned_stable_equals_hits

end J1R43Literal