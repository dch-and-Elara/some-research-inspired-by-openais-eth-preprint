import V8PooledRangeSimple

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

namespace V8PooledRange

def rawSeats {V E : Type*} (G : Graph V E) (p : ThreePorts G) : E × Bool ≃ V × Fin 3 :=
  ((incidenceEquiv G).symm.trans (Equiv.sigmaCongrRight p)).trans
    (Equiv.sigmaEquivProd V (Fin 3))

private theorem edgeSlot_inj : Function.Injective edgeSlot := by decide

theorem graphPort_inj {V E : Type*} (G : Graph V E) (p : ThreePorts G) :
    Function.Injective (fun x : E × Bool => graphPort G p x.1 x.2) := by
  intro x y he
  apply (rawSeats G p).injective
  have h := Sum.inl.inj he
  apply Prod.ext
  · exact congrArg (Prod.fst : V × Fin 5 → V) h
  · exact edgeSlot_inj (congrArg (Prod.snd : V × Fin 5 → Fin 5) h)

private def slotVar (a : Bool ⊕ Fin 3) : Fin 5 :=
  a.elim (fun b => if b then 2 else 0) edgeSlot

private def slotInv (a : Fin 5) : Bool ⊕ Fin 3 :=
  Fin.cases (.inl false) (fun t => Fin.cases (.inr 0)
    (fun t => Fin.cases (.inl true) (fun t => Fin.cases (.inr 1) (fun _ => .inr 2) t) t) t) a

private def slotEquiv : Bool ⊕ Fin 3 ≃ Fin 5 where
  toFun := slotVar
  invFun := slotInv
  left_inv := by decide
  right_inv := by decide

abbrev OriginalOccurrence (V E : Type*) := ((V × Bool) ⊕ (E × Bool)) ⊕ Bool

/-- Allocating the original occurrences is a bijection onto physical
variables. Cycles are added *after* this allocation. -/
def originalOccurrenceEquiv {V E : Type*} (G : Graph V E) (p : ThreePorts G) :
    OriginalOccurrence V E ≃ Variable V :=
  ((Equiv.sumCongr (Equiv.refl (V × Bool)) (rawSeats G p)).sumCongr (Equiv.refl Bool)).trans
    (((Equiv.prodSumDistrib V Bool (Fin 3)).symm.trans
      (Equiv.prodCongr (Equiv.refl V) slotEquiv)).sumCongr (Equiv.refl Bool))

def clausePort {V E : Type*} (G : Graph V E) (p : ThreePorts G) (s : V → Bool)
    (q : ClauseId V E × Bool) : Variable V :=
  let c := clauses G p s q.1
  if q.2 then c.2.1 else c.1.1

/-- Addresses of the original clauses are disjoint, and every physical
copy is used in one and only one original literal. -/
theorem original_switch_port {V E : Type*} (G : Graph V E) (p : ThreePorts G) (s : V → Bool)
    (v : V) (b : Bool) :
    originalOccurrenceEquiv G p (.inl (.inl (v,b))) =
      clausePort G p s (.inl (.inr v),b) := by cases b <;> rfl

theorem original_edge_port {V E : Type*} (G : Graph V E) (p : ThreePorts G) (s : V → Bool)
    (e : E) (b : Bool) :
    originalOccurrenceEquiv G p (.inl (.inr (e,b))) =
      clausePort G p s (.inr (.inl e),b) := by cases b <;> rfl

theorem original_detached_port {V E : Type*} (G : Graph V E) (p : ThreePorts G) (s : V → Bool)
    (b : Bool) :
    originalOccurrenceEquiv G p (.inr b) =
      clausePort G p s (.inr (.inr ()),b) := by cases b <;> rfl

def splitOccurrences (V E : Type*) :
    ClauseId V E × Bool ≃ ((V × Fin 5) × Bool) ⊕ OriginalOccurrence V E where
  toFun
    | (.inl (.inl (v,i)),b) => .inl ((v,if b then i+1 else i),b)
    | (.inl (.inr v),b) => .inr (.inl (.inl (v,b)))
    | (.inr (.inl e),b) => .inr (.inl (.inr (e,b)))
    | (.inr (.inr _),b) => .inr (.inr b)
  invFun
    | .inl ((v,i),b) => (.inl (.inl (v,if b then i-1 else i)),b)
    | .inr (.inl (.inl (v,b))) => (.inl (.inr v),b)
    | .inr (.inl (.inr (e,b))) => (.inr (.inl e),b)
    | .inr (.inr b) => (.inr (.inr ()),b)
  left_inv := by rintro ⟨((⟨v,j⟩ | v) | (e | ⟨⟩)),b⟩ <;> cases b <;> simp
  right_inv := by rintro (⟨⟨v,j⟩,b⟩ | ((⟨v,b⟩ | ⟨e,b⟩) | b)) <;> cases b <;> simp

def occurrenceChart {V E : Type*} (G : Graph V E) (p : ThreePorts G) :
    ClauseId V E × Bool ≃ ((V × Fin 5) × Bool) ⊕ Variable V :=
  (splitOccurrences V E).trans (Equiv.sumCongr (Equiv.refl _) (originalOccurrenceEquiv G p))

theorem occurrenceChart_projects {V E : Type*} (G : Graph V E) (p : ThreePorts G)
    (s : V → Bool) (q : ClauseId V E × Bool) :
    ((occurrenceChart G p) q).elim (fun t => Sum.inl t.1) id = clausePort G p s q := by
  rcases q with ⟨((⟨v,j⟩ | v) | (e | ⟨⟩)),b⟩ <;> cases b <;> rfl

/-- Counts the distinct syntactic clause-port occurrences of each variable
before any network contraction. -/
theorem variable_degree {V E : Type*} [Fintype V] [Fintype E]
    (G : Graph V E) (p : ThreePorts G) (s : V → Bool) (x : Variable V) :
    Nat.card {q : ClauseId V E × Bool // clausePort G p s q = x} =
      x.elim (fun _ => 3) (fun _ => 1) := by
  classical
  let D : ((V × Fin 5) × Bool) ⊕ Variable V → Variable V :=
    fun z => z.elim (fun t => Sum.inl t.1) id
  let e : {q : ClauseId V E × Bool // clausePort G p s q = x} ≃
      {r : ((V × Fin 5) × Bool) ⊕ Variable V // D r = x} :=
    (occurrenceChart G p).subtypeEquiv (fun q => (occurrenceChart_projects G p s q).symm ▸ Iff.rfl)
  rw [Nat.card_congr e]
  rcases x with (x | x)
  · let g : {r : ((V × Fin 5) × Bool) ⊕ Variable V // D r = .inl x} ≃ (Bool ⊕ Unit) := {
      toFun := fun r => r.val.elim (fun z => Sum.inl z.2) (fun _ => Sum.inr ())
      invFun := fun q => q.elim (fun b => ⟨.inl (x,b),rfl⟩) (fun _ => ⟨.inr (.inl x),rfl⟩)
      left_inv := by
        rintro ⟨(⟨a,b⟩ | y),h⟩
        · have ha : a=x := Sum.inl.inj h
          subst a
          rfl
        · have hy : y=.inl x := h
          subst y
          rfl
      right_inv := by rintro (b | ⟨⟩) <;> rfl }
    rw [Nat.card_congr g]
    simp [Nat.card_eq_fintype_card]
  · let g : {r : ((V × Fin 5) × Bool) ⊕ Variable V // D r = .inr x} ≃ Unit := {
      toFun := fun _ => ()
      invFun := fun _ => ⟨.inr (.inr x),rfl⟩
      left_inv := by
        rintro ⟨(⟨a,b⟩ | y),h⟩
        · exact False.elim (Sum.noConfusion h)
        · have hy : y=.inr x := h
          subst y
          rfl
      right_inv := by rintro ⟨⟩; rfl }
    rw [Nat.card_congr g]
    simp [Nat.card_eq_fintype_card]

def support {V E : Type*} [DecidableEq V] (G : Graph V E) (p : ThreePorts G) (s : V → Bool)
    (i : ClauseId V E) : Finset (Variable V) :=
  {(clauses G p s i).1.1,(clauses G p s i).2.1}

private theorem finite_cycle_distinct (i : Fin 5) : i ≠ i+1 := by decide +revert

theorem support_width {V E : Type*} [DecidableEq V] (G : Graph V E) (p : ThreePorts G)
    (s : V → Bool) (i : ClauseId V E) : (support G p s i).card = 2 := by
  rcases i with ((⟨v,j⟩ | v) | (e | ⟨⟩))
  · have h : (Sum.inl (v,j) : Variable V) ≠ .inl (v,j+1) :=
      fun he => finite_cycle_distinct j (congrArg Prod.snd (Sum.inl.inj he))
    simp [support,clauses,h]
  · have h : (Sum.inl (v,(0 : Fin 5)) : Variable V) ≠ .inl (v,2) := by simp
    simp [support,clauses,h]
  · have hn : graphPort G p e false ≠ graphPort G p e true := by
      intro he
      have h := congrArg Prod.snd (graphPort_inj G p (a₁ := (e,false)) (a₂ := (e,true)) he)
      cases h
    simp [support,clauses,hn]
  · simp [support,clauses]

theorem source_register_dimensions {V E : Type*} [Fintype V] [Fintype E]
    (G : Graph V E) (p : ThreePorts G) :
    (2*(2*Fintype.card (ClauseId V E)) = 30*Fintype.card V+4) ∧
    (Fintype.card (Variable V) + Fintype.card (ClauseId V E) = 25*Fintype.card V/2+3) ∧
    (Fintype.card (Variable V) + 1 = 5*Fintype.card V+3) := by
  have h := literal_ports_count G p
  rw [variable_count]
  omega

#print axioms rawSeats
#print axioms graphPort_inj
#print axioms originalOccurrenceEquiv
#print axioms original_switch_port
#print axioms original_edge_port
#print axioms original_detached_port
#print axioms occurrenceChart_projects
#print axioms variable_degree
#print axioms support_width
#print axioms source_register_dimensions

end V8PooledRange
