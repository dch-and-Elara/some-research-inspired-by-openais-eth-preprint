
import MainClonedCNF
import S11Schedule

namespace S11

open scoped BigOperators

variable {V : Type*}

/-- An incidence is a literal position in the actual clause list.
    These lists have distinct variables in each clause. -/
abbrev Incidence (f : Std.Sat.CNF V) := Σ c : Fin f.length, Fin (f.get c).length
abbrev Wire (f : Std.Sat.CNF V) := Incidence f × Bool

def variableOf (f : Std.Sat.CNF V) (i : Incidence f) : V := ((f.get i.1).get i.2).1
def polarity (f : Std.Sat.CNF V) (i : Incidence f) : Bool := ((f.get i.1).get i.2).2

/-- The old endpoint of each subdivided wire, with its clause or variable
    equality tensor. The other endpoint is the subdivision vertex i. -/
def oldEndpoint (f : Std.Sat.CNF V) (w : Wire f) : V ⊕ Fin f.length :=
  if w.2 then Sum.inl (variableOf f w.1) else Sum.inr w.1.1

def subdivision (f : Std.Sat.CNF V) (w : Wire f) : Incidence f := w.1

/-- The output of the Boolean equality and clause tensors, as a predicate
    on wire bits whose product is the indicator of this predicate. -/
def WireSat (f : Std.Sat.CNF V) (w : Wire f → Bool) : Prop :=
  (∀ i, w (i,false) = w (i,true)) ∧
  (∀ i j, variableOf f i = variableOf f j → w (i,true) = w (j,true)) ∧
  (∀ c : Fin f.length, ∃ j : Fin (f.get c).length, w (⟨c,j⟩,false) = polarity f ⟨c,j⟩)

private theorem clauses_iff (f : Std.Sat.CNF V) (x : V → Bool) :
    Std.Sat.CNF.Sat x f ↔
      ∀ c : Fin f.length, ∃ j : Fin (f.get c).length, x (variableOf f ⟨c,j⟩) = polarity f ⟨c,j⟩ := by
  simp only [Std.Sat.CNF.sat_def, Std.Sat.CNF.eval, List.all_eq_true]
  constructor
  · intro h c
    obtain ⟨l, hl, hx⟩ := List.any_eq_true.1 (h (f.get c) (List.get_mem _ _))
    obtain ⟨j, hj⟩ := List.get_of_mem hl
    refine ⟨j, ?_⟩
    change x ((f.get c).get j).1 = ((f.get c).get j).2
    rw [hj]
    simpa using hx
  · intro h cl hc
    obtain ⟨c,rfl⟩ := List.get_of_mem hc
    obtain ⟨j,hj⟩ := h c
    exact List.any_eq_true.2 ⟨(f.get c).get j, List.get_mem _ _, by
      simpa [variableOf, polarity] using hj⟩

/-- Unique corresponding wire assignment, including both halves of
    every subdivided incidence. -/
noncomputable def subdivisionEquiv (f : Std.Sat.CNF V)
    (occurs : Function.Surjective (variableOf f)) :
    {x : V → Bool // Std.Sat.CNF.Sat x f} ≃ {w : Wire f → Bool // WireSat f w} where
  toFun x := ⟨fun i => x.val (variableOf f i.1), (fun _ => rfl), (fun _ _ h => congrArg x.val h),
    (clauses_iff f x.val).1 x.property⟩
  invFun w := ⟨fun v => w.val (Classical.choose (occurs v),true), by
    apply (clauses_iff f _).2
    intro c
    obtain ⟨j,h⟩ := w.property.2.2 c
    refine ⟨j, ?_⟩
    change w.val (Classical.choose (occurs (variableOf f ⟨c,j⟩)), true) = _
    rw [w.property.2.1 _ ⟨c,j⟩ (Classical.choose_spec (occurs (variableOf f ⟨c,j⟩))),
      ← w.property.1]
    exact h⟩
  left_inv x := by
    apply Subtype.ext
    funext v
    exact congrArg x.val (Classical.choose_spec (occurs v))
  right_inv w := by
    apply Subtype.ext
    funext j
    obtain ⟨i,b⟩ := j
    have h := w.property.2.1 _ i (Classical.choose_spec (occurs (variableOf f i)))
    cases b
    · exact h.trans (w.property.1 i).symm
    · exact h

variable [Fintype V] [DecidableEq V]

noncomputable def contraction (f : Std.Sat.CNF V) : ℕ := by
  classical
  exact Fintype.card {w : Wire f → Bool // WireSat f w}

omit [DecidableEq V] in
theorem contraction_eq_modelCount (f : Std.Sat.CNF V)
    (occurs : Function.Surjective (variableOf f)) :
    contraction f = PinnedCNF.modelCount f := by
  classical
  unfold contraction PinnedCNF.modelCount
  rw [← Fintype.card_congr (subdivisionEquiv f occurs), Fintype.card_subtype]
  simp [Std.Sat.CNF.sat_def]

private theorem sum_length_get {A : Type*} (f : List (List A)) :
    (∑ c : Fin f.length, (f.get c).length) = (f.map List.length).sum := by
  induction f with
  | nil => simp
  | cons x xs ih =>
    change (∑ c : Fin (xs.length + 1), ((x :: xs).get c).length) = _
    rw [Fin.sum_univ_succ]
    simpa using congrArg (fun n => x.length + n) ih

omit [Fintype V] [DecidableEq V] in
theorem wire_card (f : Std.Sat.CNF V) :
    Fintype.card (Wire f) = 2 * MainClonedCNF.literalCount f := by
  rw [Fintype.card_prod, Fintype.card_sigma, Fintype.card_bool]
  simp only [Fintype.card_fin]
  rw [sum_length_get]
  exact Nat.mul_comm _ _

noncomputable def cloned (E : Finset (V × V)) (regular : ∀ v, GraphCutMoments.degree E v = 3)
    (σ : V → Bool) : Std.Sat.CNF (V × Fin 4) :=
  MainClonedCNF.formula E (MainClonedCNF.leftSlot E regular) (MainClonedCNF.rightSlot E regular) σ

omit [DecidableEq V] [Fintype V] in
private theorem cycle_mem (v : V) (i : Fin 4) :
    ∃ cl ∈ MainClonedCNF.cycle v, ((v,i),false) ∈ cl := by
  fin_cases i <;> simp [MainClonedCNF.cycle]

theorem every_clone_occurs (E : Finset (V × V)) (regular : ∀ v, GraphCutMoments.degree E v = 3)
    (σ : V → Bool) : Function.Surjective (variableOf (cloned E regular σ)) := by
  rintro ⟨v,i⟩
  obtain ⟨cl,hcl,hl⟩ := cycle_mem v i
  have h : cl ∈ cloned E regular σ := by
    change cl ∈ _ ++ _ ++ _
    apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_flatMap.2 ⟨v, Finset.mem_toList.2 (Finset.mem_univ _), hcl⟩
  obtain ⟨c,rfl⟩ := List.get_of_mem h
  obtain ⟨j,hj⟩ := List.get_of_mem hl
  exact ⟨⟨c,j⟩, congrArg Prod.fst hj⟩

theorem cloned_wire_count (E : Finset (V × V)) (regular : ∀ v, GraphCutMoments.degree E v = 3)
    (σ : V → Bool) : Fintype.card (Wire (cloned E regular σ)) = 24 * Fintype.card V := by
  rw [wire_card, cloned, MainClonedCNF.literalCount_eq_ports, MainClonedCNF.port_card E regular]
  omega

theorem cloned_contraction (E : Finset (V × V)) (regular : ∀ v, GraphCutMoments.degree E v = 3)
    (σ : V → Bool) : contraction (cloned E regular σ) =
      PinnedCNF.modelCount (PinnedCNF.formula E σ) := by
  rw [contraction_eq_modelCount _ (every_clone_occurs E regular σ)]
  exact MainClonedCNF.modelCount_cloned .. 

omit [Fintype V] [DecidableEq V] in
private theorem cycle_clauses (l : List V) :
    (l.flatMap MainClonedCNF.cycle).length = 4 * l.length := by
  induction l with
  | nil => simp
  | cons v vs ih =>
    rw [List.flatMap_cons, List.length_append, ih]
    have h : (MainClonedCNF.cycle v).length = 4 := rfl
    simp [h]
    omega

theorem cloned_dimensions (E : Finset (V × V)) (regular : ∀ v, GraphCutMoments.degree E v = 3)
    (σ : V → Bool) :
    Fintype.card (V × Fin 4) = 4 * Fintype.card V ∧
    2 * (cloned E regular σ).length = 13 * Fintype.card V := by
  constructor
  · simp [mul_comm]
  have he := GraphCutMoments.regular_edge_count E 3 regular
  simp only [cloned, MainClonedCNF.formula, List.length_append, List.length_map,
    cycle_clauses, Finset.length_toList, Finset.card_univ, Finset.card_attach]
  omega

def clauseBranch (n m : ℕ) : Prop := m ≤ n * Nat.clog 2 (Nat.clog 2 n)

theorem cloned_dispatch {N n m : ℕ} (hn : n = 4*N) (hm : 2*m = 13*N)
    (hnu : 2 ≤ Nat.clog 2 (Nat.clog 2 n)) : clauseBranch n m := by
  unfold clauseBranch
  have h := Nat.mul_le_mul_left n hnu
  omega

#print axioms subdivisionEquiv
#print axioms contraction_eq_modelCount
#print axioms wire_card
#print axioms every_clone_occurs
#print axioms cloned_wire_count
#print axioms cloned_contraction
#print axioms cloned_dimensions
#print axioms cloned_dispatch

end S11

