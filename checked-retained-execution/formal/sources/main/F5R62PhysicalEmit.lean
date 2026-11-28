import F5R62PhysicalEmitBase
import F5R61GeneratedCycles
import Mathlib.Data.List.Nodup

/-! Emission of the actual generated copy cycles into the same signed
literal language as the F1 base and detached rows. -/
namespace F5R62.PhysicalEmit
set_option autoImplicit false
set_option warningAsError true
open F5R60 F5R61

variable {V E T : Type}

def implicationRow (p q : PrivatePos V E T) : Row V E T :=
  [privateLit p false,privateLit q true]

def chainRows : PrivatePos V E T → List (PrivatePos V E T) → CNF V E T
  | _,[] => []
  | p,q::rest => implicationRow p q :: chainRows q rest

def cycleRowsAt {G : RequestGraph V E T} (D : PrintedCycles G) (n : Logical V T) :
    CNF V E T :=
  chainRows (D.first n) (D.rest n) ++ [implicationRow (D.last n) (D.first n)]

theorem implication_clause_exact (b : PrivatePos V E T → Bool) (d : Bool × Bool)
    (p q : PrivatePos V E T) :
    rowEval (assignment b d) (implicationRow p q)=true ↔ Imp (b p) (b q) := by
  cases hp : b p <;> cases hq : b q <;>
    simp [implicationRow,privateLit,rowEval,assignment,literalBit,Imp,hp,hq]

theorem chain_rows_exact (b : PrivatePos V E T → Bool) (d : Bool × Bool)
    (xs : List (PrivatePos V E T)) {p z : PrivatePos V E T}
    (valid : Chain (fun (_ : PrivatePos V E T) => false) p xs z) :
    CnfSat (assignment b d) (chainRows p xs) ↔ Chain b p xs z := by
  induction xs generalizing p with
  | nil =>
    change p=z at valid
    subst z
    simp [chainRows,CnfSat,Chain]
  | cons q qs ih =>
    change Imp false false ∧ Chain (fun (_ : PrivatePos V E T) => false) q qs z at valid
    rw [chainRows,sat_cons,implication_clause_exact]
    change (Imp (b p) (b q) ∧ CnfSat (assignment b d) (chainRows q qs)) ↔
      Imp (b p) (b q) ∧ Chain b q qs z
    rw [ih (p:=q) valid.2]

theorem one_cycle_rows_exact {G : RequestGraph V E T} (D : PrintedCycles G)
    (b : PrivatePos V E T → Bool) (d : Bool × Bool) (n : Logical V T) :
    CnfSat (assignment b d) (cycleRowsAt D n) ↔ ClosedCycle b (D.first n) (D.rest n) (D.last n) := by
  simp only [cycleRowsAt,sat_append,sat_single,implication_clause_exact,
    chain_rows_exact b d (D.rest n) (D.chainOrder n),ClosedCycle]

def logicalListing (v : Listing V) (t : Listing T) : Listing (Logical V T) where
  elems := v.elems.map Sum.inl ++ t.elems.map Sum.inr
  once := by
    apply List.Nodup.append
    · exact v.once.map (fun _ _ h => Sum.inl.inj h)
    · exact t.once.map (fun _ _ h => Sum.inr.inj h)
    · intro a hleft hright
      obtain ⟨_,_,h₁⟩ := List.mem_map.mp hleft
      obtain ⟨_,_,h₂⟩ := List.mem_map.mp hright
      exact Sum.noConfusion (h₁.trans h₂.symm)
  all := by
    intro n
    cases n with
    | inl x => exact List.mem_append_left _ (List.mem_map.mpr ⟨x,v.all x,rfl⟩)
    | inr x => exact List.mem_append_right _ (List.mem_map.mpr ⟨x,t.all x,rfl⟩)

def cycleRows {G : RequestGraph V E T} (D : PrintedCycles G)
    (v : Listing V) (t : Listing T) : CNF V E T :=
  (logicalListing v t).elems.flatMap (cycleRowsAt D)

theorem all_cycle_rows_exact {G : RequestGraph V E T} (D : PrintedCycles G)
    (v : Listing V) (t : Listing T) (b : PrivatePos V E T → Bool) (d : Bool × Bool) :
    CnfSat (assignment b d) (cycleRows D v t) ↔
    ∀ n, ClosedCycle b (D.first n) (D.rest n) (D.last n) := by
  simp only [cycleRows,sat_flatMap,one_cycle_rows_exact]

theorem reconstruct_assignment (a : PhysicalVar V E T → Bool) :
    assignment (fun p => a (.inl p)) (a (.inr false),a (.inr true)) = a := by
  funext val
  cases val with
  | inl p => rfl
  | inr d => cases d <;> rfl

variable [DecidableEq V] [DecidableEq T]
variable (G : RequestGraph V E T) (v : Listing V) (e : Listing E) (t : Listing T)

def f1ActualCNF : CNF V E T :=
  baseRows G v e t ++ (cycleRows (generatedPrintedCycles G v e t) v t ++ [detachedRow])

theorem actual_f1_cnf_assignment_exact (b : PrivatePos V E T → Bool) (d : Bool × Bool) :
    CnfSat (assignment b d) (f1ActualCNF G v e t) ↔
    PhysicalPrinted G (generatedPrintedCycles G v e t) b d := by
  simp only [f1ActualCNF,sat_append,sat_single,all_base_rows_exact,all_cycle_rows_exact,
    detached_row_exact,PhysicalPrinted]

theorem actual_f1_boolean_evaluation_exact (b : PrivatePos V E T → Bool) (d : Bool × Bool) :
    (f1ActualCNF G v e t).all (rowEval (assignment b d))=true ↔
    PhysicalPrinted G (generatedPrintedCycles G v e t) b d :=
  (list_boolean_test _ _).trans (actual_f1_cnf_assignment_exact G v e t b d)

theorem emitted_iff_physical :
    (∃ a, CnfSat a (f1ActualCNF G v e t)) ↔
    ∃ b d, PhysicalPrinted G (generatedPrintedCycles G v e t) b d := by
  constructor
  · rintro ⟨a,h⟩
    rw [← reconstruct_assignment a] at h
    exact ⟨(fun p => a (.inl p)),(a (.inr false),a (.inr true)),
      (actual_f1_cnf_assignment_exact G v e t _ _).1 h⟩
  · rintro ⟨b,d,h⟩
    exact ⟨assignment b d,(actual_f1_cnf_assignment_exact G v e t b d).2 h⟩

theorem emitted_f1_decides_allowed :
    (∃ a, CnfSat a (f1ActualCNF G v e t)) ↔ ∃ x, Allowed G x :=
  (emitted_iff_physical G v e t).trans (generated_physical_F1_decides_allowed G v e t)

#print axioms implication_clause_exact
#print axioms chain_rows_exact
#print axioms one_cycle_rows_exact
#print axioms logicalListing
#print axioms all_cycle_rows_exact
#print axioms reconstruct_assignment
#print axioms f1ActualCNF
#print axioms actual_f1_cnf_assignment_exact
#print axioms actual_f1_boolean_evaluation_exact
#print axioms emitted_iff_physical
#print axioms emitted_f1_decides_allowed
end F5R62.PhysicalEmit
