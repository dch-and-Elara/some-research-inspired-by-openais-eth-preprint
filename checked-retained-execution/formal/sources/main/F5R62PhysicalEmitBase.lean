import F5R61ActualCycleLists
import F5R60SourceSizes
import F5R59ConflictCore

/-! F1's literal rows, on the same original physical tags as
F5R60.BasePositions. The final clause uses the two disjoint detached
variables of F5R60.PhysicalVar. -/
namespace F5R62.PhysicalEmit
set_option autoImplicit false
set_option warningAsError true
open F5R60 F5R61

variable {V E T : Type}

abbrev Signed (V E T : Type) := F5R59.Literal (PhysicalVar V E T)
abbrev Row (V E T : Type) := List (Signed V E T)
abbrev CNF (V E T : Type) := List (Row V E T)

def privateLit (p : PrivatePos V E T) (positive : Bool) : Signed V E T :=
  ⟨.inl p,positive⟩

def detachedLit (which : Bool) : Signed V E T := ⟨.inr which,true⟩

def assignment (b : PrivatePos V E T → Bool) (d : Bool × Bool) : PhysicalVar V E T → Bool
  | .inl p => b p
  | .inr false => d.1
  | .inr true => d.2

def rowEval (a : PhysicalVar V E T → Bool) : Row V E T → Bool
  | [] => false
  | l::r => literalBit l.positive (a l.var) || rowEval a r

def CnfSat (a : PhysicalVar V E T → Bool) (F : CNF V E T) : Prop :=
  ∀ row ∈ F, rowEval a row=true

theorem sat_cons (a : PhysicalVar V E T → Bool) (r : Row V E T) (F : CNF V E T) :
    CnfSat a (r::F) ↔ rowEval a r=true ∧ CnfSat a F := by
  simp [CnfSat]

theorem sat_single (a : PhysicalVar V E T → Bool) (r : Row V E T) :
    CnfSat a [r] ↔ rowEval a r=true := by
  simp [CnfSat]

theorem sat_append (a : PhysicalVar V E T → Bool) (A B : CNF V E T) :
    CnfSat a (A++B) ↔ CnfSat a A ∧ CnfSat a B := by
  simp only [CnfSat,List.mem_append,or_imp,forall_and]

theorem sat_map {I : Type} (a : PhysicalVar V E T → Bool)
    (L : Listing I) (f : I → Row V E T) :
    CnfSat a (L.elems.map f) ↔ ∀ i, rowEval a (f i)=true := by
  constructor
  · intro h i
    exact h _ (List.mem_map.mpr ⟨i,L.all i,rfl⟩)
  · intro h r hr
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
    exact h i

theorem sat_flatMap {I : Type} (a : PhysicalVar V E T → Bool)
    (L : Listing I) (f : I → CNF V E T) :
    CnfSat a (L.elems.flatMap f) ↔ ∀ i, CnfSat a (f i) := by
  constructor
  · intro h i r hr
    exact h r (List.mem_flatMap.mpr ⟨i,L.all i,hr⟩)
  · intro h r hr
    obtain ⟨i,_,mem⟩ := List.mem_flatMap.mp hr
    exact h i r mem

theorem list_boolean_test (a : PhysicalVar V E T → Bool) (F : CNF V E T) :
    F.all (rowEval a)=true ↔ CnfSat a F := by
  exact List.all_eq_true

def switchRow (G : RequestGraph V E T) (v : V) : Row V E T :=
  [privateLit (.sw v 0) false,privateLit (.sw v 1) (G.available v)]

def conflictRow (e : E) : Row V E T :=
  [privateLit (.cf e 0) false,privateLit (.cf e 1) false]

def edgeRow (G : RequestGraph V E T) (e : E) : Row V E T :=
  [privateLit (.er e 0) true,privateLit (.er e 1) true,privateLit (.er e 2) (G.edgeActive e)]

def edgeRows (G : RequestGraph V E T) (e : E) : CNF V E T :=
  [conflictRow e,edgeRow G e]

def tripleRows (G : RequestGraph V E T) (t : T) : CNF V E T :=
  [[privateLit (.tr t 0) false,privateLit (.tr t 1) true],
   [privateLit (.tr t 2) false,privateLit (.tr t 3) true],
   [privateLit (.tr t 4) true,privateLit (.tr t 5) true,privateLit (.tr t 6) false],
   [privateLit (.tr t 7) true,privateLit (.tr t 8) true,privateLit (.tr t 9) (G.tripleActive t)]]

def detachedRow : Row V E T := [detachedLit false,detachedLit true]

def baseRows (G : RequestGraph V E T) (v : Listing V) (e : Listing E) (t : Listing T) : CNF V E T :=
  v.elems.map (switchRow G) ++ (e.elems.flatMap (edgeRows G) ++ t.elems.flatMap (tripleRows G))

theorem switch_row_exact (G : RequestGraph V E T) (v : V)
    (b : PrivatePos V E T → Bool) (d : Bool × Bool) :
    rowEval (assignment b d) (switchRow G v) =
      ((!b (.sw v 0)) || literalBit (G.available v) (b (.sw v 1))) := by
  simp [switchRow,privateLit,rowEval,assignment,literalBit]

theorem edge_rows_exact (G : RequestGraph V E T) (e : E)
    (b : PrivatePos V E T → Bool) (d : Bool × Bool) :
    CnfSat (assignment b d) (edgeRows G e) ↔
    ((!b (.cf e 0)) || (!b (.cf e 1))) = true ∧
    (b (.er e 0) || b (.er e 1) || literalBit (G.edgeActive e) (b (.er e 2))) = true := by
  simp only [edgeRows,sat_cons]
  simp [CnfSat,conflictRow,edgeRow,privateLit,rowEval,assignment,literalBit,Bool.or_assoc]

theorem triple_rows_exact (G : RequestGraph V E T) (t : T)
    (b : PrivatePos V E T → Bool) (d : Bool × Bool) :
    CnfSat (assignment b d) (tripleRows G t) ↔
    ((!b (.tr t 0)) || b (.tr t 1)) = true ∧
    ((!b (.tr t 2)) || b (.tr t 3)) = true ∧
    (b (.tr t 4) || b (.tr t 5) || (!b (.tr t 6))) = true ∧
    (b (.tr t 7) || b (.tr t 8) || literalBit (G.tripleActive t) (b (.tr t 9))) = true := by
  simp only [tripleRows,sat_cons]
  simp [CnfSat,privateLit,rowEval,assignment,literalBit,Bool.or_assoc]

theorem detached_row_exact (b : PrivatePos V E T → Bool) (d : Bool × Bool) :
    rowEval (assignment b d) detachedRow = (d.1 || d.2) := by
  simp [detachedRow,detachedLit,rowEval,assignment,literalBit]

theorem all_base_rows_exact (G : RequestGraph V E T)
    (v : Listing V) (e : Listing E) (t : Listing T)
    (b : PrivatePos V E T → Bool) (d : Bool × Bool) :
    CnfSat (assignment b d) (baseRows G v e t) ↔ BasePositions G b := by
  rw [baseRows,sat_append,sat_append,sat_map,sat_flatMap,sat_flatMap]
  simp only [switch_row_exact,edge_rows_exact,triple_rows_exact,BasePositions]
  constructor
  · rintro ⟨sw,e,tr⟩
    exact ⟨sw,fun x => (e x).1,fun x => (e x).2,tr⟩
  · rintro ⟨sw,cf,er,tr⟩
    exact ⟨sw,fun x => ⟨cf x,er x⟩,tr⟩

#print axioms rowEval
#print axioms CnfSat
#print axioms baseRows
#print axioms list_boolean_test
#print axioms switch_row_exact
#print axioms edge_rows_exact
#print axioms triple_rows_exact
#print axioms detached_row_exact
#print axioms all_base_rows_exact
end F5R62.PhysicalEmit
