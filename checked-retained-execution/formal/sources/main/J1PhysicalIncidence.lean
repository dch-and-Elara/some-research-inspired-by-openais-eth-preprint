import J1MainSourceCertificate
import MainClonedCNF
import Mathlib.Tactic

/-! The literal four-clone MAIN input satisfies the actual hypotheses of the
J1 certificate. Port numbering is the same as the compiled cloned CNF. -/
namespace J1PhysicalIncidence

open scoped BigOperators
open MainClonedCNF J1MainSourceCollision J1MainSourcePlacement J1MainSourceBridge
open J1MainSourceLabels
universe u b i s

variable {V : Type u} [DecidableEq V]
abbrev Variable (V : Type u) := V × Fin 4
abbrev Factor (E : Finset (V×V)) := V ⊕ (E ⊕ (V × Fin 4))

def portFactor (E : Finset (V×V)) : Port E → Factor E
  | .inl v => .inl v
  | .inr (.inl (e,_)) => .inr (.inl e)
  | .inr (.inr (v,j,_)) => .inr (.inr (v,j))

def factorBit (E : Finset (V×V)) : Port E → Bool
  | .inl _ => false
  | .inr (.inl (_,b)) => b
  | .inr (.inr (_,_,b)) => b

def portAtFactor (E : Finset (V×V)) : Factor E × Bool → Port E
  | (.inl v,_) => .inl v
  | (.inr (.inl e),b) => .inr (.inl (e,b))
  | (.inr (.inr (v,j)),b) => .inr (.inr (v,j,b))

omit [DecidableEq V] in
theorem factor_decode (E : Finset (V×V)) (p : Port E) :
    portAtFactor E (portFactor E p,factorBit E p) = p := by
  rcases p with v | ⟨⟨e,b⟩|⟨v,j,b⟩⟩ <;> rfl

def portRole (E : Finset (V×V)) : Port E → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 0
  | .inr (.inr (_,_,b)) => if b then 2 else 1

section VariableNumbering
variable [Fintype V]
variable (E : Finset (V×V)) (reg : ∀ v, GraphCutMoments.degree E v = 3)

noncomputable def portVar : Port E → Variable V
  | .inl v => (v,0)
  | .inr (.inl (e,b)) =>
    if b then (e.1.2,rightSlot E reg e) else (e.1.1,leftSlot E reg e)
  | .inr (.inr (v,j,b)) => (v,if b then j+1 else j)

def fromOriented (v : V) : EndpointSlot E v → Port E
  | .inl e => .inr (.inl (⟨e.1,(Finset.mem_filter.mp e.2).1⟩,false))
  | .inr e => .inr (.inl (⟨e.1,(Finset.mem_filter.mp e.2).1⟩,true))

noncomputable def fromExternal (x : Variable V) : Port E :=
  Fin.cases (Sum.inl x.1) (fun i => fromOriented E x.1 ((edgeNumber E reg x.1).symm i)) x.2

omit [Fintype V] in
theorem source_left_lookup (e : E) :
    fromExternal E reg (e.1.1,leftSlot E reg e) = Sum.inr (Sum.inl (e,false)) := by
  unfold fromExternal leftSlot
  simp [fromOriented]

omit [Fintype V] in
theorem source_right_lookup (e : E) :
    fromExternal E reg (e.1.2,rightSlot E reg e) = Sum.inr (Sum.inl (e,true)) := by
  unfold fromExternal rightSlot
  simp [fromOriented]

noncomputable def portAtVar (x : Variable V) (r : Fin 3) : Port E :=
  if r=0 then fromExternal E reg x else
  if r=1 then Sum.inr (Sum.inr (x.1,x.2,false)) else
    Sum.inr (Sum.inr (x.1,x.2-1,true))

omit [Fintype V] in
/-- A clone has precisely one external role (pin or edge) and two oriented
cycle roles. Decoding the role recovers every physical literal occurrence. -/
theorem variable_decode (p : Port E) :
    portAtVar E reg (portVar E reg p) (portRole E p) = p := by
  rcases p with v | ⟨⟨e,b⟩|⟨v,j,b⟩⟩
  · simp [portAtVar,portVar,portRole,fromExternal]
  · cases b
    · simpa [portAtVar,portVar,portRole] using source_left_lookup E reg e
    · simpa [portAtVar,portVar,portRole] using source_right_lookup E reg e
  · cases b
    · simp [portAtVar,portVar,portRole]
    · simp [portAtVar,portVar,portRole]

omit [DecidableEq V] in
theorem variables_card : Fintype.card (Variable V) = 4 * Fintype.card V := by
  simp [Variable,Nat.mul_comm]

theorem var_degree_bound (x : Variable V) : (varFibre (portVar E reg) x).card ≤ 3 := by
  let fibre := varFibre (portVar E reg) x
  have he (p : fibre) : portVar E reg p.val = x := by
    exact (Finset.mem_filter.mp p.property).2
  have hinj : Function.Injective (fun p : fibre => portRole E p.val) := by
    intro p q h
    apply Subtype.ext
    change portRole E p.val = portRole E q.val at h
    rw [← variable_decode E reg p.val,← variable_decode E reg q.val,he p,he q,h]
  simpa [fibre] using Fintype.card_le_of_injective _ hinj

end VariableNumbering

variable [Fintype V] in
theorem factor_scope_bound (E : Finset (V×V)) (q : Factor E) :
    (facFibre (portFactor E) q).card ≤ 2 := by
  let fibre := facFibre (portFactor E) q
  have he (p : fibre) : portFactor E p.val = q := by
    exact (Finset.mem_filter.mp p.property).2
  have hinj : Function.Injective (fun p : fibre => factorBit E p.val) := by
    intro p r h
    apply Subtype.ext
    change factorBit E p.val = factorBit E r.val at h
    rw [← factor_decode E p.val,← factor_decode E r.val,he p,he r,h]
  simpa [fibre] using Fintype.card_le_of_injective _ hinj

section Tags
variable [Fintype V] {B : Type b} [DecidableEq B]
variable (E : Finset (V×V)) (block : V → B)

def tie : Factor E → Option B
  | .inl v => some (block v)
  | .inr _ => none

omit [DecidableEq V] in
theorem actual_tag_fibre (b : B) :
    tagFibre (tie E block ∘ portFactor E) b =
      (Finset.univ.filter (fun v => block v=b)).map (pinPort E) := by
  ext p
  rcases p with v | ⟨⟨e,c⟩|⟨v,j,c⟩⟩ <;>
    simp [tagFibre,tie,portFactor,pinPort,Function.comp_apply]

omit [DecidableEq V] [DecidableEq B] in
theorem number_tied_slots :
    (tiedSlots (tie E block ∘ portFactor E)).card = Fintype.card V := by
  have hf : tiedSlots (tie E block ∘ portFactor E) = Finset.univ.map (pinPort E) := by
    ext p
    rcases p with v | ⟨⟨e,c⟩|⟨v,j,c⟩⟩ <;>
      simp [tiedSlots,tie,portFactor,pinPort,Function.comp_apply]
  simp [hf]

omit [DecidableEq V] in
theorem tag_degree_bound (hblock : ∀ b, (Finset.univ.filter (fun v => block v=b)).card ≤ 3)
    (b : B) : (tagFibre (tie E block ∘ portFactor E) b).card ≤ 3 := by
  rw [actual_tag_fibre,Finset.card_map]
  exact hblock b

end Tags

section LiteralCompiler
variable [Fintype V]
variable (E : Finset (V×V)) (reg : ∀ v, GraphCutMoments.degree E v = 3)

def portsInFactor : Factor E → List (Port E)
  | .inl v => [.inl v]
  | .inr (.inl e) => [.inr (.inl (e,false)),.inr (.inl (e,true))]
  | .inr (.inr (v,j)) => [.inr (.inr (v,j,false)),.inr (.inr (v,j,true))]

def signAt (σ : V → Bool) : Port E → Bool
  | .inl v => σ v
  | .inr (.inl _) => true
  | .inr (.inr (_,_,b)) => b

noncomputable def literalClause (σ : V → Bool) (q : Factor E) :
    Std.Sat.CNF.Clause (Variable V) :=
  (portsInFactor E q).map (fun p => (portVar E reg p,signAt E σ p))

noncomputable def compiledCNF (σ : V → Bool) : Std.Sat.CNF (Variable V) :=
  (Finset.univ.toList.flatMap (fun v =>
    (List.finRange 4).map (fun j => literalClause E reg σ (.inr (.inr (v,j)))))) ++
  (Finset.univ.toList.map (fun v => literalClause E reg σ (.inl v))) ++
  (E.attach.toList.map (fun e => literalClause E reg σ (.inr (.inl e))))

theorem literal_to_original_formula (σ : V → Bool) :
    compiledCNF E reg σ = MainClonedCNF.formula E (leftSlot E reg) (rightSlot E reg) σ := by
  have hc (v : V) :
      (List.finRange 4).map (fun j => literalClause E reg σ (.inr (.inr (v,j)))) =
        MainClonedCNF.cycle v := rfl
  have hp (v : V) : literalClause E reg σ (.inl v) = [((v,0),σ v)] := rfl
  have he (e : E) : literalClause E reg σ (.inr (.inl e)) =
      [((e.1.1,leftSlot E reg e),true),((e.1.2,rightSlot E reg e),true)] := rfl
  simp [compiledCNF,MainClonedCNF.formula,hc,hp,he]

end LiteralCompiler

#print axioms factor_decode
#print axioms variable_decode
#print axioms var_degree_bound
#print axioms factor_scope_bound
#print axioms actual_tag_fibre
#print axioms number_tied_slots
#print axioms tag_degree_bound
#print axioms literal_to_original_formula
end J1PhysicalIncidence
