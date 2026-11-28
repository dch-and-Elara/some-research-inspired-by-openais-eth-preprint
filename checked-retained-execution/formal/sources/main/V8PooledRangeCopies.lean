import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic

/-!
Genuine five-copy binary CNFs of v8, Section F1/C5-C6. Variables, literal
signs, physical edge ports, and the detached clause are defined explicitly.
-/
set_option autoImplicit false
set_option warningAsError true

namespace V8PooledRange

abbrev Graph (V E : Type*) := E → Bool → V

abbrev Incidence {V E : Type*} (G : Graph V E) (v : V) :=
  {q : E × Bool // G q.1 q.2 = v}

abbrev ThreePorts {V E : Type*} (G : Graph V E) :=
  (v : V) → Incidence G v ≃ Fin 3

abbrev Variable (V : Type*) := (V × Fin 5) ⊕ Bool

abbrev ClauseId (V E : Type*) := ((V × Fin 5) ⊕ V) ⊕ (E ⊕ Unit)

abbrev Literal (V : Type*) := Variable V × Bool

abbrev Clause (V : Type*) := Literal V × Literal V

def edgeSlot (j : Fin 3) : Fin 5 :=
  Fin.cases 1 (fun t => Fin.cases 3 (fun _ => 4) t) j

def graphPort {V E : Type*} (G : Graph V E) (p : ThreePorts G)
    (e : E) (b : Bool) : Variable V :=
  .inl (G e b, edgeSlot (p (G e b) ⟨(e,b), rfl⟩))

def clauses {V E : Type*} (G : Graph V E) (p : ThreePorts G) (s : V → Bool) :
    ClauseId V E → Clause V
  | .inl (.inl (v,j)) => (((.inl (v,j)),false), ((.inl (v,j+1)),true))
  | .inl (.inr v) => (((.inl (v,0)),false), ((.inl (v,2)),s v))
  | .inr (.inl e) => ((graphPort G p e false,false), (graphPort G p e true,false))
  | .inr (.inr _) => ((.inr false,true), (.inr true,true))

def Clause.holds {V : Type*} (a : Variable V → Bool) (c : Clause V) : Prop :=
  a c.1.1 = c.1.2 ∨ a c.2.1 = c.2.2

def model {V E : Type*} (G : Graph V E) (p : ThreePorts G) (s : V → Bool)
    (a : Variable V → Bool) : Prop :=
  ∀ i, (clauses G p s i).holds a

def allowed {V E : Type*} (G : Graph V E) (s x : V → Bool) : Prop :=
  (∀ v, x v = false ∨ s v = true) ∧ (∀ e, x (G e false) = false ∨ x (G e true) = false)

abbrev Independent {V E : Type*} (G : Graph V E) (s : V → Bool) :=
  {x : V → Bool // allowed G s x}

abbrev Detached := {a : Bool × Bool // a.1 = true ∨ a.2 = true}

abbrev PhysicalModels {V E : Type*} (G : Graph V E) (p : ThreePorts G) (s : V → Bool) :=
  {a : Variable V → Bool // model G p s a}

noncomputable instance {V E : Type*} [Fintype V] (G : Graph V E) (s : V → Bool) :
    Fintype (Independent G s) := Fintype.ofFinite _

noncomputable instance {V E : Type*} [Fintype V]
    (G : Graph V E) (p : ThreePorts G) (s : V → Bool) :
    Fintype (PhysicalModels G p s) := Fintype.ofFinite _

theorem cycle_constant (b : Fin 5 → Bool)
    (h : ∀ j, b j = false ∨ b (j+1) = true) : ∀ j, b j = b 0 := by
  have h01 : b 0 = false ∨ b 1 = true := h 0
  have h12 : b 1 = false ∨ b 2 = true := h 1
  have h23 : b 2 = false ∨ b 3 = true := h 2
  have h34 : b 3 = false ∨ b 4 = true := h 3
  have h40 : b 4 = false ∨ b 0 = true := h 4
  intro j
  cases h0 : b 0
  · have h4 := h40.resolve_right (by simp [h0])
    have h3 := h34.resolve_right (by simp [h4])
    have h2 := h23.resolve_right (by simp [h3])
    have h1 := h12.resolve_right (by simp [h2])
    fin_cases j <;> simp_all
  · have h1 := h01.resolve_left (by simp [h0])
    have h2 := h12.resolve_left (by simp [h1])
    have h3 := h23.resolve_left (by simp [h2])
    have h4 := h34.resolve_left (by simp [h3])
    fin_cases j <;> simp_all

theorem model_shape {V E : Type*} {G : Graph V E} {p : ThreePorts G} {s : V → Bool}
    (a : Variable V → Bool) :
    model G p s a ↔
      (∀ v j, a (.inl (v,j)) = a (.inl (v,0))) ∧
      allowed G s (fun v => a (.inl (v,0))) ∧
      (a (.inr false) = true ∨ a (.inr true) = true) := by
  constructor
  · intro h
    have hcol : ∀ v j, a (.inl (v,j)) = a (.inl (v,0)) :=
      fun v => cycle_constant (fun j => a (.inl (v,j))) (fun j => h (.inl (.inl (v,j))))
    refine ⟨hcol, ⟨?_, ?_⟩, h (.inr (.inr ()))⟩
    · intro v
      have hv : a (.inl (v,0)) = false ∨ a (.inl (v,2)) = s v := h (.inl (.inr v))
      rw [hcol v 2] at hv
      cases hb : a (.inl (v,0)) <;> simp_all
    · intro e
      have he : a (graphPort G p e false) = false ∨ a (graphPort G p e true) = false :=
        h (.inr (.inl e))
      simpa only [graphPort, hcol] using he
  · rintro ⟨hcol, ⟨hv, he⟩, hd⟩ i
    rcases i with ((⟨v,j⟩ | v) | (e | _))
    · change a (.inl (v,j)) = false ∨ a (.inl (v,j+1)) = true
      rw [hcol v j, hcol v (j+1)]
      cases a (.inl (v,0)) <;> simp
    · change a (.inl (v,0)) = false ∨ a (.inl (v,2)) = s v
      rw [hcol v 2]
      rcases hv v with hf | ht
      · exact Or.inl hf
      · rw [ht]
        cases a (.inl (v,0)) <;> simp
    · change a (graphPort G p e false) = false ∨ a (graphPort G p e true) = false
      simpa only [graphPort, hcol] using he e
    · exact hd

/-- Exact physical model equivalence, for these clauses and no virtual duplicate counts. -/
def modelEquiv {V E : Type*} (G : Graph V E) (p : ThreePorts G) (s : V → Bool) :
    PhysicalModels G p s ≃ Independent G s × Detached where
  toFun a :=
    (⟨fun v => a.val (.inl (v,0)), ((model_shape a.val).mp a.property).2.1⟩,
     ⟨(a.val (.inr false), a.val (.inr true)), ((model_shape a.val).mp a.property).2.2⟩)
  invFun q :=
    ⟨Sum.elim (fun v => q.1.val v.1) (fun b => if b then q.2.val.2 else q.2.val.1),
      (model_shape _).mpr ⟨fun _ _ => rfl, q.1.property, q.2.property⟩⟩
  left_inv := by
    intro a
    apply Subtype.ext
    funext v
    rcases v with (⟨v,j⟩ | b)
    · exact (((model_shape a.val).mp a.property).1 v j).symm
    · cases b <;> rfl
  right_inv := by
    intro a
    rfl

theorem detached_card : Fintype.card Detached = 3 := by decide

noncomputable def satCount {V E : Type*} [Fintype V]
    (G : Graph V E) (p : ThreePorts G) (s : V → Bool) : ℕ :=
  Fintype.card (PhysicalModels G p s)

theorem five_copy_count {V E : Type*} [Fintype V]
    (G : Graph V E) (p : ThreePorts G) (s : V → Bool) :
    satCount G p s = 3 * Fintype.card (Independent G s) := by
  unfold satCount
  rw [Fintype.card_congr (modelEquiv G p s), Fintype.card_prod, detached_card, Nat.mul_comm]

theorem variable_count (V : Type*) [Fintype V] :
    Fintype.card (Variable V) = 5 * Fintype.card V + 2 := by
  simp [Nat.mul_comm]

def incidenceEquiv {V E : Type*} (G : Graph V E) :
    (Σ v, Incidence G v) ≃ E × Bool where
  toFun p := p.2.val
  invFun q := ⟨G q.1 q.2, ⟨q, rfl⟩⟩
  left_inv := by rintro ⟨v,⟨⟨e,b⟩,rfl⟩⟩; rfl
  right_inv _ := rfl

theorem twice_edge_count {V E : Type*} [Fintype V] [Fintype E]
    (G : Graph V E) (p : ThreePorts G) : 2 * Fintype.card E = 3 * Fintype.card V := by
  classical
  let u : (Σ v, Incidence G v) ≃ V × Fin 3 :=
    (Equiv.sigmaCongrRight p).trans (Equiv.sigmaEquivProd V (Fin 3))
  have h := Fintype.card_congr ((incidenceEquiv G).symm.trans u)
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] at h
  omega

theorem literal_ports_count {V E : Type*} [Fintype V] [Fintype E]
    (G : Graph V E) (p : ThreePorts G) :
    2 * Fintype.card (ClauseId V E) = 15 * Fintype.card V + 2 := by
  have h := twice_edge_count G p
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit]
  omega

#print axioms cycle_constant
#print axioms model_shape
#print axioms modelEquiv
#print axioms detached_card
#print axioms five_copy_count
#print axioms variable_count
#print axioms twice_edge_count
#print axioms literal_ports_count

end V8PooledRange
