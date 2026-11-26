import S8DoubleSampling

namespace S8.Uncloned

open GraphCutMoments SourceDensity
open scoped BigOperators
set_option maxHeartbeats 1000000

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Incidence (E : Finset (V × V)) := V ⊕ (E × Bool)
abbrev OriginalEdge (E : Finset (V × V)) := Incidence E ⊕ V
abbrev Wire (E : Finset (V × V)) := OriginalEdge E × Bool
abbrev Vertex (E : Finset (V × V)) := (V × Bool) ⊕ (V ⊕ E)

/-- Bit 0 is a pin's half and port position. The three incidence slots of
the cubic graph use the other three half/port positions. -/
def incidenceBits : Unit ⊕ Fin 3 ≃ Bool × Bool where
  toFun
    | .inl _ => (false,false)
    | .inr i => (decide (i ≠ 0), decide (i ≠ 1))
  invFun
    | (false,false) => .inl ()
    | (false,true) => .inr 0
    | (true,false) => .inr 1
    | (true,true) => .inr 2
  left_inv := by
    rintro (⟨⟩ | i)
    · rfl
    · fin_cases i <;> decide
  right_inv := by rintro ⟨a,b⟩; cases a <;> cases b <;> decide

noncomputable def slot (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) :
    Incidence E → V × (Bool × Bool)
  | .inl v => (v, incidenceBits (.inl ()))
  | .inr (e,b) =>
      let q := Triangle.endpoint E reg e b
      (q.1, incidenceBits (.inr q.2))

theorem slot_injective (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) :
    Function.Injective (slot E reg) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (congrArg Prod.fst h)
    | inr b =>
      exact False.elim (Sum.noConfusion (incidenceBits.injective (congrArg Prod.snd h)))
  | inr a =>
    cases b with
    | inl b =>
      exact False.elim (Sum.noConfusion (incidenceBits.injective (congrArg Prod.snd h)))
    | inr b =>
      have hi := incidenceBits.injective (congrArg Prod.snd h)
      have hf : (Triangle.endpoint E reg a.1 a.2).1 = (Triangle.endpoint E reg b.1 b.2).1 :=
        congrArg (fun z : V × (Bool × Bool) => z.1) h
      have hp : Triangle.endpoint E reg a.1 a.2 = Triangle.endpoint E reg b.1 b.2 :=
        Prod.ext hf (Sum.inr.inj hi)
      exact congrArg Sum.inr (Triangle.endpoint_injective E reg hp)

/-- The d=4 tree consists of two equality vertices joined by one internal
edge. Each original edge is subdivided once. -/
noncomputable def old (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) :
    Wire E → Vertex E
  | (.inl p,false) => .inl ((slot E reg p).1,(slot E reg p).2.1)
  | (.inl (.inl v),true) => .inr (.inl v)
  | (.inl (.inr (e,_)),true) => .inr (.inr e)
  | (.inr v,b) => .inl (v,b)

def pin (E : Finset (V × V)) : V ↪ Wire E where
  toFun v := (.inl (.inl v),true)
  inj' := by intro _ _ h; simpa using h

noncomputable def portTag (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) :
    Wire E → Fin 3
  | (.inl p,false) => if (slot E reg p).2.2 then 2 else 1
  | (.inl (.inl _),true) => 0
  | (.inl (.inr (_,b)),true) => if b then 1 else 0
  | (.inr _,_) => 0

theorem old_degree (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) (v : Vertex E) :
    fiberCount (old E reg) v ≤ 3 := by
  classical
  rw [fiberCount, ← Fintype.card_fin 3, ← Finset.card_univ]
  apply Finset.card_le_card_of_injOn (portTag E reg)
  · exact fun _ _ => Finset.mem_univ _
  · intro a ha b hb hh
    have h := (Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm
    clear ha hb
    rcases a with ⟨p,x⟩
    rcases b with ⟨q,y⟩
    rcases p with ((a | ⟨e,s⟩) | a) <;> rcases q with ((b | ⟨f,t⟩) | b)
    all_goals cases x <;> cases y
    all_goals
      simp only [old, portTag, Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq, reduceCtorEq] at h hh ⊢
    all_goals try (solve | tauto | split at hh <;> omega)
    all_goals try (solve | cases s <;> cases t <;> simp_all only [Bool.false_eq_true, if_false,
      if_true, Fin.isValue, and_true, and_false, Nat.reduceEq] <;> omega)
    all_goals try (solve | cases s <;> cases t <;> simp_all)
    all_goals
      have same := slot_injective E reg (Prod.ext h.1 (Prod.ext h.2 (by
        split at hh <;> split at hh <;> simp_all only [Bool.not_eq_true] <;> omega)))
      simp_all

theorem wire_count (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) :
    Fintype.card (Wire E) = 10 * Fintype.card V := by
  have h := regular_edge_count E 3 reg
  simp only [Wire, OriginalEdge, Incidence, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_bool, Fintype.card_coe]
  omega

theorem pin_wire_iff (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) (w : Wire E) (v : V) :
    old E reg w = .inr (.inl v) ↔ pin E v = w := by
  rcases w with ⟨(p | x),b⟩
  · cases b
    · cases p <;> simp [old,pin]
    · rcases p with (x | ⟨e,c⟩) <;> simp [old,pin,eq_comm]
  · cases b <;> simp [old,pin]

noncomputable def vertexOf (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) :
    OriginalEdge E → V
  | .inl p => (slot E reg p).1
  | .inr v => v

/-- Exact Boolean relations at all subdivision vertices, both equality
halves of each variable, the pins, and the OR clause factors. -/
def accepts (E : Finset (V × V)) (reg : ∀ v, degree E v = 3)
    (σ : V → Bool) (a : Wire E → Bool) : Prop :=
  (∀ p, a (p,false) = a (p,true)) ∧
  (∀ q : Incidence E, a (.inl q,false) =
    a (.inr (slot E reg q).1,(slot E reg q).2.1)) ∧
  (∀ v, a (pin E v) = σ v) ∧
  (∀ e : E, a (.inl (.inr (e,false)),true) = true ∨ a (.inl (.inr (e,true)),true) = true)

theorem accepts_iff (E : Finset (V × V)) (reg : ∀ v, degree E v = 3)
    (σ : V → Bool) (a : Wire E → Bool) :
    accepts E reg σ a ↔
      a = (fun w => σ (vertexOf E reg w.1)) ∧ PinnedCNF.AllEdges E σ := by
  have hx (e : E) : (slot E reg (.inr (e,false))).1 = e.1.1 := rfl
  have hy (e : E) : (slot E reg (.inr (e,true))).1 = e.1.2 := rfl
  constructor
  · rintro ⟨sub,eq,pins,clauses⟩
    have hpin (v : V) : a ((.inr v),false) = σ v := by
      have hh := eq (.inl v)
      change a (.inl (.inl v),false) = a (.inr v,false) at hh
      rw [← hh, sub]
      exact pins v
    have links (v : V) (b : Bool) : a (.inr v,b) = σ v := by
      cases b
      · exact hpin v
      · exact (sub (.inr v)).symm.trans (hpin v)
    have hh : a = fun w => σ (vertexOf E reg w.1) := by
      funext w
      rcases w with ⟨p,b⟩
      cases p with
      | inr v => exact links v b
      | inl q =>
        have eq' := (eq q).trans (links _ _)
        cases b
        · exact eq'
        · exact (sub (.inl q)).symm.trans eq'
    refine ⟨hh,fun e he => ?_⟩
    have hc := clauses ⟨e,he⟩
    rw [hh] at hc
    exact hc
  · rintro ⟨rfl,h⟩
    exact ⟨fun _ => rfl,fun _ => rfl, fun _ => rfl,fun e => h e.1 e.2⟩

noncomputable def networkCount (E : Finset (V × V)) (reg : ∀ v, degree E v = 3)
    (σ : V → Bool) : ℕ := by
  classical exact (Finset.univ.filter (accepts E reg σ)).card

theorem countUncloned (E : Finset (V × V)) (reg : ∀ v, degree E v = 3) (σ : V → Bool) :
    networkCount E reg σ = PinnedCNF.modelCount (PinnedCNF.formula E σ) := by
  classical
  rw [PinnedCNF.count_eq_indicator, networkCount]
  have hh : Finset.univ.filter (accepts E reg σ) =
      if PinnedCNF.AllEdges E σ then {fun w : Wire E => σ (vertexOf E reg w.1)} else ∅ := by
    ext a
    by_cases h : PinnedCNF.AllEdges E σ <;> simp [accepts_iff, h]
  rw [hh]
  split <;> simp

#print axioms old_degree
#print axioms wire_count
#print axioms pin_wire_iff
#print axioms accepts_iff
#print axioms countUncloned

end S8.Uncloned




