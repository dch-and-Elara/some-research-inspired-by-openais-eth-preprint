import V8PooledRangeCopies
import CaterpillarRange

set_option autoImplicit false
set_option warningAsError true

namespace V8PooledRange

abbrev Word := CaterpillarRange.Word
abbrev Marking := CaterpillarRange.Marking

/-- Position zero is the right endpoint, matching the archived recurrence.
The second coordinate distinguishes a spine vertex from its own leaf. -/
abbrev Tree (k : ℕ) := Fin (k+1) × Bool

def TreeEdge : ℕ → Type
  | 0 => Unit
  | k+1 => Bool ⊕ TreeEdge k

instance treeEdgeFintype : (k : ℕ) → Fintype (TreeEdge k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k+1 => by
    letI := treeEdgeFintype k
    exact inferInstanceAs (Fintype (Bool ⊕ TreeEdge k))

def treeEnds : (k : ℕ) → Graph (Tree k) (TreeEdge k)
  | 0, _, b => (0,b)
  | _+1, .inl false, b => (0,b)
  | k+1, .inl true, b => ((if b then (0 : Fin (k+1)).succ else 0), false)
  | k+1, .inr e, b => ((treeEnds k e b).1.succ, (treeEnds k e b).2)

def treeEnabled : (k : ℕ) → Word k → Bool → Tree k → Bool
  | 0, _, b, (_,l) => if l then true else b
  | k+1, w, b, (i,l) => Fin.cases (if l then w 0 else b)
      (fun j => treeEnabled k (fun n => w n.succ) true (j,l)) i

def treeValues : (k : ℕ) → Bool → Marking k → Tree k → Bool
  | 0, b, m, (_,l) => if l then m else b
  | k+1, b, m, (i,l) => Fin.cases (if l then m.1 else b)
      (fun j => treeValues k m.2.1 m.2.2 (j,l)) i

def treeMarking : (k : ℕ) → (Tree k → Bool) → Bool × Marking k
  | 0, x => (x (0,false),x (0,true))
  | k+1, x =>
    let q := treeMarking k (fun v => x (v.1.succ,v.2))
    (x (0,false),x (0,true),q.1,q.2)

theorem treeMarking_values (k : ℕ) (e : Bool) (m : Marking k) :
    treeMarking k (treeValues k e m) = (e,m) := by
  induction k generalizing e with
  | zero => rfl
  | succ k ih =>
    change Marking (k+1) at m
    rcases (show Bool × Bool × Marking k from m) with ⟨l,p,q⟩
    change (e,l,(treeMarking k (treeValues k p q)).1,
      (treeMarking k (treeValues k p q)).2) = (e,l,p,q)
    rw [ih p q]

theorem treeValues_marking (k : ℕ) (x : Tree k → Bool) :
    treeValues k (treeMarking k x).1 (treeMarking k x).2 = x := by
  induction k with
  | zero =>
    funext v
    rcases v with ⟨i,l⟩
    have hi : i = 0 := Fin.eq_zero i
    subst i
    cases l <;> rfl
  | succ k ih =>
    funext v
    rcases v with ⟨i,l⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · cases l <;> rfl
    · exact congrFun (ih (fun v => x (v.1.succ,v.2))) (j,l)

private theorem tree_allowed_zero (w : Word 0) (b e : Bool) (m : Marking 0) :
    allowed (treeEnds 0) (treeEnabled 0 w b) (treeValues 0 e m) ↔
      (e=false ∨ b=true) ∧ CaterpillarRange.independent 0 w e m := by
  constructor
  · rintro ⟨ha,hc⟩
    refine ⟨ha (0,false),?_⟩
    have hc' : e=false ∨ m=false := hc ()
    cases e
    · trivial
    · exact hc'.resolve_left (by decide)
  · rintro ⟨he, hm⟩
    constructor
    · rintro ⟨_, l⟩
      cases l
      · exact he
      · exact Or.inr rfl
    · intro _
      change e=false ∨ m=false
      cases e
      · exact Or.inl rfl
      · exact Or.inr hm

private theorem treeAvail_step (k : ℕ) (w : Word (k+1)) (b e l p : Bool)
    (m : Marking k) :
    (∀ v, treeValues (k+1) e (l,p,m) v = false ∨ treeEnabled (k+1) w b v = true) ↔
      (e=false ∨ b=true) ∧ (l=false ∨ w 0=true) ∧
      (∀ v, treeValues k p m v = false ∨ treeEnabled k (fun i => w i.succ) true v = true) := by
  constructor
  · intro h
    exact ⟨h (0,false),h (0,true),fun v => h (v.1.succ,v.2)⟩
  · rintro ⟨h0,h1,ht⟩ ⟨i,c⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · cases c
      · exact h0
      · exact h1
    · exact ht (j,c)

theorem treeValues_left (k : ℕ) (e : Bool) (m : Marking k) :
    treeValues k e m (0,false) = e := by
  cases k <;> rfl

private theorem treeEdges_step (k : ℕ) (e l p : Bool) (m : Marking k) :
    (∀ j, treeValues (k+1) e (l,p,m) (treeEnds (k+1) j false) = false ∨
      treeValues (k+1) e (l,p,m) (treeEnds (k+1) j true) = false) ↔
        (e=false ∨ l=false) ∧ (e=false ∨ p=false) ∧
        (∀ j, treeValues k p m (treeEnds k j false) = false ∨
          treeValues k p m (treeEnds k j true) = false) := by
  change (∀ j : Bool ⊕ TreeEdge k, _) ↔ _
  constructor
  · intro h
    refine ⟨h (.inl false),?_,fun j => h (.inr j)⟩
    have hp := h (.inl true)
    simpa only [treeValues, treeEnds, Bool.true_eq, ↓reduceIte, Fin.cases_zero,
      Fin.cases_succ, Bool.false_eq_true, treeValues_left] using hp
  · rintro ⟨h0,h1,ht⟩ (c | j)
    · cases c
      · exact h0
      · simpa only [treeValues, treeEnds, Bool.true_eq, ↓reduceIte, Fin.cases_zero,
          Fin.cases_succ, Bool.false_eq_true, treeValues_left] using h1
    · exact ht j

/-- Exact equivalence with the archived C5 marking predicate. -/
theorem tree_allowed (k : ℕ) (w : Word k) (b e : Bool) (m : Marking k) :
    allowed (treeEnds k) (treeEnabled k w b) (treeValues k e m) ↔
      (e=false ∨ b=true) ∧ CaterpillarRange.independent k w e m := by
  induction k generalizing b e with
  | zero => exact tree_allowed_zero w b e m
  | succ k ih =>
    rcases (show Bool × Bool × Marking k from m) with ⟨l,p,m⟩
    change allowed (treeEnds (k+1)) (treeEnabled (k+1) w b) (treeValues (k+1) e (l,p,m)) ↔ _
    unfold allowed
    rw [treeAvail_step,treeEdges_step]
    constructor
    · rintro ⟨⟨h0,hl,ha⟩,hc,hp,he⟩
      have hi := ((ih (fun i => w i.succ) true p m).mp ⟨ha,he⟩).2
      refine ⟨h0,?_⟩
      cases e
      · exact ⟨hl,hi⟩
      · exact ⟨hc.resolve_left (by decide),hp.resolve_left (by decide),hi⟩
    · rintro ⟨h0,hi⟩
      cases e
      · obtain ⟨hl,hi⟩ := hi
        obtain ⟨ha,he⟩ := (ih (fun i => w i.succ) true p m).mpr ⟨Or.inr rfl,hi⟩
        exact ⟨⟨h0,hl,ha⟩,Or.inl rfl,Or.inl rfl,he⟩
      · obtain ⟨hl,hp,hi⟩ := hi
        obtain ⟨ha,he⟩ := (ih (fun i => w i.succ) true p m).mpr ⟨Or.inr rfl,hi⟩
        exact ⟨⟨h0,Or.inl hl,ha⟩,Or.inr hl,Or.inr hp,he⟩

abbrev EnabledMarking (k : ℕ) (w : Word k) (b : Bool) :=
  {q : Bool × Marking k // (q.1=false ∨ b=true) ∧ CaterpillarRange.independent k w q.1 q.2}

def treeMarkingEquiv (k : ℕ) (w : Word k) (b : Bool) :
    EnabledMarking k w b ≃ Independent (treeEnds k) (treeEnabled k w b) where
  toFun q := ⟨treeValues k q.val.1 q.val.2, (tree_allowed k w b _ _).mpr q.property⟩
  invFun x := ⟨treeMarking k x.val, by
    apply (tree_allowed k w b _ _).mp
    rw [treeValues_marking]
    exact x.property⟩
  left_inv q := Subtype.ext (treeMarking_values k q.val.1 q.val.2)
  right_inv x := Subtype.ext (treeValues_marking k x.val)

def aboveMarkingEquiv (k : ℕ) (w : Word k) :
    (b : Bool) → EnabledMarking k w b ≃ CaterpillarRange.EnabledSelections k w b
  | false => {
      toFun := fun q => ⟨q.val.2, by
        have h := q.property.1.resolve_right (by decide)
        simpa only [h] using q.property.2⟩
      invFun := fun q => ⟨(false,q.val),Or.inl rfl,q.property⟩
      left_inv := fun q => Subtype.ext <| Prod.ext (q.property.1.resolve_right (by decide)).symm rfl
      right_inv := fun _ => rfl }
  | true => {
      toFun := fun q => ⟨q.val.1,⟨q.val.2,q.property.2⟩⟩
      invFun := fun q => ⟨(q.1,q.2.val),Or.inr rfl,q.2.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem tree_count (k : ℕ) (w : Word k) (b : Bool) :
    3 * Fintype.card (Independent (treeEnds k) (treeEnabled k w b)) =
      CaterpillarRange.output k (w,b) := by
  rw [CaterpillarRange.output_eq_selections,
    Fintype.card_congr ((treeMarkingEquiv k w b).symm.trans (aboveMarkingEquiv k w b))]

#print axioms treeMarking_values
#print axioms treeValues_marking
#print axioms tree_allowed
#print axioms treeMarkingEquiv
#print axioms aboveMarkingEquiv
#print axioms tree_count

end V8PooledRange
