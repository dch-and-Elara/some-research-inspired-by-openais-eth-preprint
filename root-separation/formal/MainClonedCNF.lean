import MainIncidence
import Mathlib.Tactic.FinCases

/-! The concrete four-copy CNF at the direct rational entry. All literal
choices have a common syntax tree. The finite port type enumerates its
unary pins, graph-edge literals and implication-cycle literals. -/

namespace MainClonedCNF

variable {V : Type*}
open scoped BigOperators

def cycle (v : V) : Std.Sat.CNF (V × Fin 4) :=
  [[((v,0),false),((v,1),true)],
   [((v,1),false),((v,2),true)],
   [((v,2),false),((v,3),true)],
   [((v,3),false),((v,0),true)]]

private theorem cycle_bits (a b c d : Bool) :
    (a=false ∨ b=true) ∧ (b=false ∨ c=true) ∧ (c=false ∨ d=true) ∧ (d=false ∨ a=true) ↔
      b=a ∧ c=a ∧ d=a := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem cycle_sat (v : V) (x : V × Fin 4 → Bool) :
    Std.Sat.CNF.Sat x (cycle v) ↔ ∀ i, x (v,i) = x (v,0) := by
  have he : Std.Sat.CNF.Sat x (cycle v) ↔
      x (v,1) = x (v,0) ∧ x (v,2) = x (v,0) ∧ x (v,3) = x (v,0) := by
    simpa [Std.Sat.CNF.sat_def, cycle] using
      cycle_bits (x (v,0)) (x (v,1)) (x (v,2)) (x (v,3))
  rw [he]
  constructor
  · rintro ⟨h₁,h₂,h₃⟩ i
    fin_cases i
    · rfl
    · exact h₁
    · exact h₂
    · exact h₃
  · intro h
    exact ⟨h 1,h 2,h 3⟩

variable [Fintype V] [DecidableEq V]

noncomputable def formula (E : Finset (V × V)) (left right : E → Fin 4) (σ : V → Bool) :
    Std.Sat.CNF (V × Fin 4) :=
  (Finset.univ.toList.flatMap cycle) ++
    (Finset.univ.toList.map fun v => [((v,0),σ v)]) ++
    (E.attach.toList.map fun e => [((e.1.1,left e),true),((e.1.2,right e),true)])

omit [DecidableEq V] in
private theorem cycles_sat (x : V × Fin 4 → Bool) :
    Std.Sat.CNF.Sat x (Finset.univ.toList.flatMap cycle) ↔
      ∀ v i, x (v,i) = x (v,0) := by
  calc
    _ ↔ ∀ v, Std.Sat.CNF.Sat x (cycle v) := by
      simp [Std.Sat.CNF.sat_def, Std.Sat.CNF.eval, List.all_eq_true]
    _ ↔ _ := forall_congr' fun v => cycle_sat v x

omit [DecidableEq V] in
private theorem pins_sat (σ : V → Bool) (x : V × Fin 4 → Bool) :
    Std.Sat.CNF.Sat x (Finset.univ.toList.map fun v => [((v,0),σ v)]) ↔
      ∀ v, x (v,0) = σ v := by
  simp [Std.Sat.CNF.sat_def, Std.Sat.CNF.eval, List.all_eq_true]

omit [DecidableEq V] [Fintype V] in
private theorem edges_sat (E : Finset (V × V)) (left right : E → Fin 4)
    (x : V × Fin 4 → Bool) :
    Std.Sat.CNF.Sat x
      (E.attach.toList.map fun e => [((e.1.1,left e),true),((e.1.2,right e),true)]) ↔
      ∀ e : E, x (e.1.1,left e) = true ∨ x (e.1.2,right e) = true := by
  simp [Std.Sat.CNF.sat_def, Std.Sat.CNF.eval, List.all_eq_true]

omit [DecidableEq V] in
theorem sat_iff (E : Finset (V × V)) (left right : E → Fin 4)
    (σ : V → Bool) (x : V × Fin 4 → Bool) :
    Std.Sat.CNF.Sat x (formula E left right σ) ↔
      x = (fun u => σ u.1) ∧ PinnedCNF.AllEdges E σ := by
  change Std.Sat.CNF.eval x (_ ++ _ ++ _) = true ↔ _
  simp only [Std.Sat.CNF.eval_append, Bool.and_eq_true, ← Std.Sat.CNF.sat_def,
    cycles_sat, pins_sat, edges_sat]
  constructor
  · rintro ⟨⟨hc,hp⟩,he⟩
    have hx : x = fun u => σ u.1 := by
      funext u
      exact (hc u.1 u.2).trans (hp u.1)
    refine ⟨hx, ?_⟩
    intro e em
    simpa [hx] using he ⟨e,em⟩
  · rintro ⟨hx,he⟩
    subst x
    exact ⟨⟨fun _ _ => rfl, fun _ => rfl⟩, fun e => he e.1 e.2⟩

theorem modelCount_cloned (E : Finset (V × V)) (left right : E → Fin 4)
    (σ : V → Bool) :
    PinnedCNF.modelCount (formula E left right σ) =
      PinnedCNF.modelCount (PinnedCNF.formula E σ) := by
  classical
  rw [PinnedCNF.count_eq_indicator]
  have hfilter : (Finset.univ.filter fun x => (formula E left right σ).eval x = true) =
      (if PinnedCNF.AllEdges E σ then {fun u => σ u.1} else ∅) := by
    ext x
    by_cases h : PinnedCNF.AllEdges E σ <;> simp [← Std.Sat.CNF.sat_def, sat_iff, h]
  unfold PinnedCNF.modelCount
  calc
    _ = (if PinnedCNF.AllEdges E σ then {fun u : V × Fin 4 => σ u.1} else
        (∅ : Finset (V × Fin 4 → Bool))).card := by
      refine Eq.trans ?_ (congrArg Finset.card hfilter)
      apply congrArg Finset.card
      ext x
      simp
    _ = _ := by split_ifs <;> simp

/-- Each vertex has three incident edge slots; their type distinguishes the two
orientations of the stored edge. -/
abbrev EndpointSlot (E : Finset (V × V)) (v : V) :=
  (E.filter fun e => e.1=v) ⊕ (E.filter fun e => e.2=v)

omit [Fintype V] in
theorem endpoint_card (E : Finset (V × V)) (v : V) :
    Fintype.card (EndpointSlot E v) = GraphCutMoments.degree E v := by
  simp only [EndpointSlot, Fintype.card_sum, Fintype.card_coe, GraphCutMoments.degree]

/-- Choose a bijection assigning the three non-pin copies to edge incidences. -/
noncomputable def edgeNumber (E : Finset (V × V)) (hreg : ∀ v, GraphCutMoments.degree E v = 3)
    (v : V) : EndpointSlot E v ≃ Fin 3 :=
  Fintype.equivFinOfCardEq ((endpoint_card E v).trans (hreg v))

noncomputable def leftSlot (E : Finset (V × V)) (hreg : ∀ v, GraphCutMoments.degree E v = 3)
    (e : E) : Fin 4 :=
  ((edgeNumber E hreg e.1.1) (Sum.inl ⟨e.1, by simp [e.2]⟩)).succ

noncomputable def rightSlot (E : Finset (V × V)) (hreg : ∀ v, GraphCutMoments.degree E v = 3)
    (e : E) : Fin 4 :=
  ((edgeNumber E hreg e.1.2) (Sum.inr ⟨e.1, by simp [e.2]⟩)).succ

/-- One literal slot for each unary pin, two per original edge and eight
per implication cycle. -/
abbrev Port (E : Finset (V × V)) := V ⊕ ((E × Bool) ⊕ (V × Fin 4 × Bool))

def pinPort (E : Finset (V × V)) : V ↪ Port E := ⟨Sum.inl, Sum.inl_injective⟩

theorem port_card (E : Finset (V × V)) (hreg : ∀ v, GraphCutMoments.degree E v = 3) :
    Fintype.card (Port E) = 12 * Fintype.card V := by
  have he := GraphCutMoments.regular_edge_count E 3 hreg
  simp only [Port, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_bool, Fintype.card_coe]
  omega

def literalCount {U : Type*} (f : Std.Sat.CNF U) : ℕ := (f.map List.length).sum

@[simp] theorem literalCount_append {U : Type*} (f g : Std.Sat.CNF U) :
    literalCount (f++g) = literalCount f + literalCount g := by simp [literalCount]

private theorem mapped_count {U W : Type*} (l : List U) (f : U → Std.Sat.CNF.Clause W)
    (k : ℕ) (hk : ∀ u, (f u).length=k) : literalCount (l.map f) = l.length*k := by
  induction l with
  | nil => simp [literalCount]
  | cons a l ih =>
    change (f a).length + literalCount (l.map f) = (l.length+1)*k
    rw [hk a,ih,Nat.add_mul,Nat.one_mul,Nat.add_comm]

omit [Fintype V] [DecidableEq V] in
private theorem concat_cycles (l : List V) :
    literalCount (l.flatMap cycle) = l.length*8 := by
  induction l with
  | nil => simp [literalCount]
  | cons a l ih =>
    rw [List.flatMap_cons, literalCount_append, ih]
    have h : literalCount (cycle a) = 8 := rfl
    simp [h]
    omega

omit [DecidableEq V] in
theorem literalCount_eq_ports (E : Finset (V × V)) (left right : E → Fin 4) (σ : V → Bool) :
    literalCount (formula E left right σ) = Fintype.card (Port E) := by
  rw [formula,literalCount_append,literalCount_append,concat_cycles,
    mapped_count _ _ 1 (fun _ => rfl),mapped_count _ _ 2 (fun _ => rfl)]
  simp [Port]
  omega

open MainIncidence in
/-- The actual cloned count, with literal incidence and pin ports taken from
the displayed CNF, inherits the finite main group-product exponent. -/
theorem direct_cloned_group_barrier {I A T : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype A] [DecidableEq A] [Nonempty A] [Fintype T] [Nonempty V]
    (E : Finset (V × V)) (loopless : ∀ v, (v,v) ∉ E)
    (regular : ∀ v, GraphCutMoments.degree E v = 3) (γ : ℚ) (hγ : 0<γ) (hγ₁ : γ≤1)
    (expansion : ∀ U : Finset V, γ*(min U.card (Fintype.card V-U.card) : ℕ) ≤
      ((GraphCutMoments.boundary E U).card : ℚ))
    (cell : Port E → (I → A) × (I → A))
    (hload : ∀ c, (SourceDensity.fiberCount cell c : ℚ) ≤
      2 * Fintype.card (Port E) / (Fintype.card ((I → A) × (I → A)) : ℚ))
    (hA : 32 ≤ Fintype.card A)
    (hsize : 7776 * (Fintype.card I : ℚ) * (96 * (Fintype.card I : ℚ)) /
      (FiniteGrowth.coefficient γ (1/4))^2 < Fintype.card V)
    (terms : T → GroupProducts.GroupTerm (MainIncidence.labels (pinPort E) cell) ℚ)
    (hrepresentation : ∀ σ, (PinnedCNF.modelCount (formula E (leftSlot E regular)
        (rightSlot E regular) σ) : ℚ) = ∑ t, (terms t).value σ) :
    ∃ d : ℕ, (FiniteGrowth.coefficient γ (1/4) * Fintype.card V)^2 ≤
      384 * (Fintype.card I : ℚ) * (d : ℚ)^2 ∧ 2^d ≤ Fintype.card T := by
  let G : MainIncidence.Layout E (pinPort E) cell 24 :=
    {positive := by decide, ports := MainIncidence.cloned_port_budget _ _ (port_card E regular),
     maxLoad := hload, alphabet := by omega, loopless := loopless, regular := regular,
     gamma := γ, gamma_pos := hγ, gamma_le_one := hγ₁, expansion := expansion}
  let output := fun σ => (PinnedCNF.modelCount (formula E (leftSlot E regular) (rightSlot E regular) σ) : ℚ)
  have hh := MainIncidence.main_modular_group_barrier G (by norm_num [G] at ⊢; exact hsize)
    (RingHom.id ℚ) (RingHom.id ℚ) Function.injective_id output terms hrepresentation
    (fun σ => by simp [output,modelCount_cloned])
  norm_num [G] at hh ⊢
  exact hh

#print axioms cycle_sat
#print axioms sat_iff
#print axioms modelCount_cloned
#print axioms endpoint_card
#print axioms port_card
#print axioms literalCount_eq_ports
#print axioms direct_cloned_group_barrier

end MainClonedCNF
