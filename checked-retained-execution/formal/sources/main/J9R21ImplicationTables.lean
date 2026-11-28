import J9R20SameFileLiteralTables

/-! The printed CNF uses one directed implication per copy-cycle edge.
These literal clause tables differ from R20's equality-cycle variant.
The original clone-variable columns, in contrast, really are equality. -/
namespace J9R21Implication
open scoped Classical
open J7SourceLabels J7SeatSource J7PrintedParamsGraph J7ToJ8Incidence
open J8Physical LiteralPortCompiler J9R20SameFile
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4800000

variable {Pair H : Type} [Fintype Pair] [Fintype H]
variable (ends : H×Bool ≃ Pin Pair×Fin 3)
local notation "T" => column ends cycle
local notation "D" => PrintedOld Pair H

private def sigmaFibrePort {V : Type*} {P : V → Type*} (v : V) :
    {p : Sigma P // p.1 = v} ≃ P v where
  toFun p := p.prop ▸ p.val.2
  invFun x := ⟨⟨v, x⟩, rfl⟩
  left_inv := by rintro ⟨⟨p,x⟩,h⟩; change p=v at h; subst p; rfl
  right_inv _ := rfl

/-- The original binary clause fibre, with the occurrence bit of the actual
subdivision row. In particular this is not an arbitrary order on the ports. -/
def binaryPortChart (c : Binary Pair H) :
    Ports T (.inr (.inl c)) ≃ Bool :=
  (ordinaryPorts T (.inl c)).trans
    (((actualOrdinaryRoute ends cycle).subtypeEquiv
      (p:=fun w : OrdinaryWire Pair H => T w = .inr (.inl c))
      (q:=fun y : Sigma (Port (Pair:=Pair) (G:=H)) => y.1 = .inr (.inl c))
      (by intro w; rfl)).trans (sigmaFibrePort (P:=Port (Pair:=Pair) (G:=H)) (.inr (.inl c))))

theorem binaryPortChart_inverse_occurrence (c : Binary Pair H) (k : Bool) :
    ((binaryPortChart ends c).symm k).val = .inr ((c,k),false) := rfl

/-- The other wire of the same subdivision reaches the clone whose sign
is used by the indicated literal: source on false, successor on true. -/
theorem copy_occurrence_reaches_original_clone (p : Pin Pair) (i : Index) (k : Bool) :
    colNode T (Sum.inr ((Sum.inr (p,i),k),true)) =
      .inr (cloneOwner (H:=H) (p, if k then cycle i else i)) := by
  cases h : (if k then cycle i else i) <;> simp [colNode,column,route,cloneOwner,h]

def copyImplication (p : Pin Pair) (i : Index) :
    CNF (Ports T (.inr (.inl (.inr (p,i))))) :=
  let e := binaryPortChart ends (.inr (p,i))
  [[(e.symm false,false),(e.symm true,true)]]

theorem copy_implication_truth (p : Pin Pair) (i : Index)
    (x : Ports T (.inr (.inl (.inr (p,i)))) → Bool) :
    let e := binaryPortChart ends (.inr (p,i))
    satisfied (copyImplication ends p i) x = (!x (e.symm false) || x (e.symm true)) := by
  simp [copyImplication,satisfied,lit]

/-- A concrete input on this very fibre distinguishes the directed clause
from the R20 convenience world, even though complete cycles agree at origin. -/
theorem copy_table_is_not_equality (p : Pin Pair) (i : Index) :
    ∃ x : Ports T (.inr (.inl (.inr (p,i)))) → Bool,
      satisfied (copyImplication ends p i) x=true ∧
      satisfied (@fullEqualityCNF _ (Fintype.ofFinite _)) x=false := by
  let e := binaryPortChart ends (.inr (p,i))
  refine ⟨e,?_,?_⟩
  · rw [copy_implication_truth]
    simp [e]
  · cases h : satisfied (@fullEqualityCNF _ (Fintype.ofFinite _)) e with
    | false => rfl
    | true =>
      have hh := (@fullEqualityCNF_true _ (Fintype.ofFinite _) e).1 h (e.symm false) (e.symm true)
      simp at hh

/-- Typed physical old tables on the original clause/clone atlas:
OR at graph edges, one directed implication at a copy edge, and full
equality only at the two tagged types of old variable columns. -/
def literalOldTable : (v : D) → CNF (Ports T v)
  | .inl p => @fullEqualityCNF _ (Fintype.ofFinite (Ports T (.inl p)))
  | .inr (.inr x) => @fullEqualityCNF _ (Fintype.ofFinite (Ports T (.inr (.inr x))))
  | .inr (.inl (.inl e)) => @positiveOr _ (Fintype.ofFinite (Ports T (.inr (.inl (.inl e)))))
  | .inr (.inl (.inr c)) => copyImplication ends c.1 c.2

theorem literal_copy_clause (p : Pin Pair) (i : Index)
    (x : Ports T (.inr (.inl (.inr (p,i)))) → Bool) :
    let e := binaryPortChart ends (.inr (p,i))
    satisfied (literalOldTable ends (.inr (.inl (.inr (p,i))))) x =
      (!x (e.symm false) || x (e.symm true)) :=
  copy_implication_truth ends p i x

theorem literal_clone_equality (s : Pin Pair×Index)
    (x : Ports T (cloneOwner (H:=H) s) → Bool) :
    satisfied (literalOldTable ends (cloneOwner s)) x = true ↔ ∀ i j, x i = x j := by
  rcases s with ⟨p,i⟩
  cases i <;> exact @fullEqualityCNF_true _ (Fintype.ofFinite _) x

theorem literal_old_table_satisfiable (v : D) :
    ∃ x : Ports T v → Bool, satisfied (literalOldTable ends v) x=true := by
  rcases v with p | (c | x)
  · exact ⟨fun _=>false, (@fullEqualityCNF_true _ (Fintype.ofFinite _) (fun _=>false)).2 (fun _ _=>rfl)⟩
  · rcases c with e | ⟨p,i⟩
    · refine ⟨fun _=>true,?_⟩
      exact (@positiveOr_true _ (Fintype.ofFinite _) (fun _=>true)).2
        ⟨(binaryPortChart ends (.inl e)).symm false,rfl⟩
    · refine ⟨fun _=>false,?_⟩
      rw [literal_copy_clause]
      rfl
  · exact ⟨fun _=>false, (@fullEqualityCNF_true _ (Fintype.ofFinite _) (fun _=>false)).2 (fun _ _=>rfl)⟩

def implicationOldTables {Packet R : Type} {L : ℕ}
    (e : H×Bool ≃ Pin Pair×Fin 3)
    (d : Layout Packet R (Pin Pair) (PrintedOld Pair H) (Fin 64)
       (Ports (column e cycle)) L) : OldTables d :=
  fun _ v => literalOldTable e v.val

theorem implication_tables_preserve_clone_variables {Packet R : Type} {L : ℕ}
    (e : H×Bool ≃ Pin Pair×Fin 3)
    (d : Layout Packet R (Pin Pair) (PrintedOld Pair H) (Fin 64)
       (Ports (column e cycle)) L) :
    LocalCloneLaw d (implicationOldTables e d) (allCloneOwners (Pair:=Pair) (H:=H)) := by
  intro v hv x
  obtain ⟨s,hs⟩ := (mem_allCloneOwners _).1 hv
  have eq : v = cloneOwner s := Sum.inr.inj (Option.some.inj hs)
  change satisfied (literalOldTable e v) x=true ↔ _
  subst v
  exact literal_clone_equality e s x

theorem implication_tables_locally_satisfiable {Packet R : Type} {L : ℕ}
    (e : H×Bool ≃ Pin Pair×Fin 3)
    (d : Layout Packet R (Pin Pair) (PrintedOld Pair H) (Fin 64)
       (Ports (column e cycle)) L) :
    ∀ g (v : LocalColumn d g), ∃ x : LocalPort d v→Bool,
      satisfied (implicationOldTables e d g v) x=true :=
  fun _ v => literal_old_table_satisfiable e v.val

#print axioms binaryPortChart_inverse_occurrence
#print axioms copy_occurrence_reaches_original_clone
#print axioms copy_implication_truth
#print axioms copy_table_is_not_equality
#print axioms literal_copy_clause
#print axioms literal_clone_equality
#print axioms literal_old_table_satisfiable
#print axioms implication_tables_preserve_clone_variables
#print axioms implication_tables_locally_satisfiable

end
end J9R21Implication
