import S8Triangle
import S8CrossRoute
import S8Certificates
import MainIncidence

namespace S8

open scoped BigOperators
open SourceDensity GraphCutMoments EmpiricalCutMoments

variable {V I A G : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Nonempty A]

abbrev Clause (E : Finset (V × V)) := V ⊕ (E ⊕ (V × Fin 4))

/-- The literal port's factor on the actual cloned formula. -/
def portClause (E : Finset (V × V)) : MainClonedCNF.Port E → Clause E
  | .inl v => .inl v
  | .inr (.inl (e,_)) => .inr (.inl e)
  | .inr (.inr (v,i,_)) => .inr (.inr (v,i))

/-- The literal port's clone. True is the second endpoint of an OR and
    the positive literal of an implication. -/
noncomputable def portClone (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) :
    MainClonedCNF.Port E → V × Fin 4
  | .inl v => (v,0)
  | .inr (.inl (e,true)) => (e.1.2, MainClonedCNF.rightSlot E reg e)
  | .inr (.inl (e,false)) => (e.1.1, MainClonedCNF.leftSlot E reg e)
  | .inr (.inr (v,i,b)) => (v, if b then i + 1 else i)

abbrev Wire (E : Finset (V × V)) := MainClonedCNF.Port E × Bool
abbrev OldVertex (E : Finset (V × V)) := (V × Fin 4) ⊕ Clause E

def pinWire (E : Finset (V × V)) : V ↪ Wire E :=
  ⟨fun v => (MainClonedCNF.pinPort E v,true), fun _ _ h =>
    (MainClonedCNF.pinPort E).injective (congrArg Prod.fst h)⟩

noncomputable def wireOld (E : Finset (V × V)) (reg : ∀ v, degree E v = 3)
    (w : Wire E) : OldVertex E :=
  if w.2 then .inr (portClause E w.1) else .inl (portClone E reg w.1)

theorem wire_card (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) :
    Fintype.card (Wire E) = 24 * Fintype.card V := by
  simp only [Wire, Fintype.card_prod, Fintype.card_bool, MainClonedCNF.port_card E reg]
  omega

/-- Each primitive function supplies one symbol at every untied position.
    A tied pin obtains its designated coordinate from its pinGroup. -/
def pinnedWord {X : Type*} (pinClass : X → Option G) (t : I)
    (free : X → I → A) (shared : G → A) (x : X) (i : I) : A :=
  if i = t then (pinClass x).elim (free x i) shared else free x i

noncomputable def mainCell (E : Finset (V × V)) (reg : ∀ v, degree E v = 3)
    (t : I) (pinGroup : V → G) (vars : V × Fin 4 → I → A) (factors : Clause E → I → A)
    (shared : G → A) (p : MainClonedCNF.Port E) : (I → A) × (I → A) :=
  (vars (portClone E reg p), pinnedWord (fun x => x.elim (some ∘ pinGroup) (fun _ => none))
    t factors shared (portClause E p))

noncomputable def appendixCell (E : Finset (V × V)) (reg : ∀ v, degree E v = 3)
    (t : I) (pinGroup : V → G) (old : OldVertex E → I → A)
    (sub : MainClonedCNF.Port E → I → A) (shared : G → A) (w : Wire E) :
    (I → A) × (I → A) :=
  (pinnedWord (fun x => x.elim (fun _ => none) (fun c => c.elim (some ∘ pinGroup) (fun _ => none)))
    t old shared (wireOld E reg w), sub w.1)

@[simp] theorem main_pin_tied (E : Finset (V × V)) (reg : ∀ v, degree E v = 3)
    (t : I) (pinGroup : V → G) (vars : V × Fin 4 → I → A) (factors : Clause E → I → A)
    (shared : G → A) (v : V) :
    (mainCell E reg t pinGroup vars factors shared (MainClonedCNF.pinPort E v)).2 t = shared (pinGroup v) := by
  simp [mainCell, pinnedWord, portClause, MainClonedCNF.pinPort]

@[simp] theorem appendix_pin_tied (E : Finset (V × V)) (reg : ∀ v, degree E v = 3)
    (kept : Finset I) (t : kept) (pinGroup : V → G) (old : OldVertex E → I → A)
    (sub : MainClonedCNF.Port E → I → A) (shared : G → A) (v : V) :
    firstCoordinates kept (appendixCell E reg t.1 pinGroup old sub shared (pinWire E v)) t =
      shared (pinGroup v) := by
  simp [firstCoordinates, appendixCell, pinnedWord, pinWire, wireOld, portClause, MainClonedCNF.pinPort]

section Marginals
variable [Nonempty V]

theorem main_pin_bounds (E : Finset (V × V)) (reg : ∀ v, degree E v = 3)
    (cell : MainClonedCNF.Port E → (I → A) × (I → A))
    (load : ∀ c, (fiberCount cell c : ℚ) ≤ 2 * Fintype.card (MainClonedCNF.Port E) /
      (Fintype.card ((I → A) × (I → A)) : ℚ))
    (alphabet : 32 ≤ Fintype.card A) :
    (∀ x, empiricalLaw (fun v => (cell (MainClonedCNF.pinPort E v)).2) x ≤
      24 * ProductVariance.uniformWeight (I → A)) ∧
    (∀ i a, empiricalLaw (fun v => (cell (MainClonedCNF.pinPort E v)).2 i) a ≤ 3/4) := by
  have ports : 2 * Fintype.card (MainClonedCNF.Port E) ≤ 24 * Fintype.card V := by
    rw [MainClonedCNF.port_card E reg]; omega
  constructor
  · exact MainIncidence.project_marked_incidence (MainClonedCNF.pinPort E) cell 24 ports load
      Prod.snd _ MainIncidence.factor_word_fiber
  · intro i a
    refine (MainIncidence.project_marked_incidence (MainClonedCNF.pinPort E) cell 24 ports load
      (fun c => c.2 i) _ (MainIncidence.factor_symbol_fiber i) a).trans ?_
    have h : (32 : ℚ) ≤ Fintype.card A := by exact_mod_cast alphabet
    unfold ProductVariance.uniformWeight
    rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
    linarith

/-- Projection to the retained R0 coordinates, with the physical 24N-wire
    network and exact alphabet size 64. -/
theorem appendix_pin_bounds (E : Finset (V × V)) (reg : ∀ v, degree E v = 3)
    (cell : Wire E → (I → A) × (I → A)) (kept : Finset I) (Δ : ℚ)
    (cert : CollisionCertificate cell Δ) (alphabet : Fintype.card A = 64) :
    (∀ x, empiricalLaw (fun v => firstCoordinates kept (cell (pinWire E v))) x ≤
      48 * ProductVariance.uniformWeight (kept → A)) ∧
    (∀ i : kept, ∀ a, empiricalLaw (fun v => (cell (pinWire E v)).1 i.1) a ≤ 3/4) := by
  have ports : 2 * Fintype.card (Wire E) ≤ 48 * Fintype.card V := by rw [wire_card E reg]; omega
  have load := port_cell_bound cell Δ cert
  constructor
  · exact MainIncidence.project_marked_incidence (pinWire E) cell 48 ports load
      (firstCoordinates kept) _ (ordered_cell_projection_regular kept)
  · intro i a
    refine (MainIncidence.project_marked_incidence (pinWire E) cell 48 ports load
      (fun c => c.1 i.1) _ (BalancedUnion.single_coordinate_fiber i.1) a).trans ?_
    norm_num [ProductVariance.uniformWeight, alphabet]

end Marginals

#print axioms wire_card
#print axioms main_pin_tied
#print axioms appendix_pin_tied
#print axioms main_pin_bounds
#print axioms appendix_pin_bounds

end S8

