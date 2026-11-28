import F5R62PhysicalEmitBase
import F5R61ForbiddenClassification
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.Nodup

/-! Actual emitted F1 original rows, each recovered by its real owner
key. Signs are those of the emitter; all disjointness below is on
physical variable occurrences, not just on signed literal strings. -/
namespace F5R62.Normalization
open F5R60 F5R61 F5R62.PhysicalEmit
set_option autoImplicit false
set_option linter.unusedSimpArgs false
variable {V E T : Type}

def rowVars (row : Row V E T) : List (PhysicalVar V E T) :=
  row.map F5R59.Literal.var

def rowOfKey (G : RequestGraph V E T) : OriginalClauseKey V E T → Row V E T
  | .vertexSwitch v => switchRow G v
  | .edgeConflict e => conflictRow e
  | .edgeRequest e => edgeRow G e
  | .tripleClause t j => (tripleRows G t)[j.val]'(by exact j.isLt)

def edgeKeys (e : E) : List (OriginalClauseKey V E T) :=
  [.edgeConflict e,.edgeRequest e]

def tripleKeys (t : T) : List (OriginalClauseKey V E T) :=
  [.tripleClause t 0,.tripleClause t 1,.tripleClause t 2,.tripleClause t 3]

def originalKeys (v : Listing V) (e : Listing E) (t : Listing T) :
    List (OriginalClauseKey V E T) :=
  v.elems.map OriginalClauseKey.vertexSwitch ++
    (e.elems.flatMap edgeKeys ++ t.elems.flatMap tripleKeys)

private theorem edge_key_rows (G : RequestGraph V E T) (e : E) :
    (edgeKeys e).map (rowOfKey G)=edgeRows G e := rfl

private theorem triple_key_rows (G : RequestGraph V E T) (t : T) :
    (tripleKeys t).map (rowOfKey G)=tripleRows G t := rfl

theorem base_rows_are_keyed (G : RequestGraph V E T)
    (v : Listing V) (e : Listing E) (t : Listing T) :
    baseRows G v e t=(originalKeys v e t).map (rowOfKey G) := by
  simp [baseRows,originalKeys,List.map_flatMap,List.map_map,Function.comp_def,
    edge_key_rows,triple_key_rows,rowOfKey]

theorem keyed_row_width (G : RequestGraph V E T) (k : OriginalClauseKey V E T) :
    (rowOfKey G k).length=2 ∨ (rowOfKey G k).length=3 := by
  cases k with
  | vertexSwitch v => exact Or.inl rfl
  | edgeConflict e => exact Or.inl rfl
  | edgeRequest e => exact Or.inr rfl
  | tripleClause t i =>
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr rfl

theorem keyed_row_two_or_more (G : RequestGraph V E T) (k : OriginalClauseKey V E T) :
    2≤(rowOfKey G k).length := by
  rcases keyed_row_width G k with h|h
  · rw [h]
  · rw [h]; decide

theorem keyed_variables_distinct (G : RequestGraph V E T) (k : OriginalClauseKey V E T) :
    (rowVars (rowOfKey G k)).Nodup := by
  cases k with
  | vertexSwitch v => simp [rowVars,rowOfKey,switchRow,privateLit]
  | edgeConflict e => simp [rowVars,rowOfKey,conflictRow,privateLit]
  | edgeRequest e => simp [rowVars,rowOfKey,edgeRow,privateLit]
  | tripleClause t i =>
    fin_cases i <;> simp [rowVars,rowOfKey,tripleRows,privateLit]

theorem keyed_variable_belongs_to_owner (G : RequestGraph V E T)
    (k : OriginalClauseKey V E T) (a : PhysicalVar V E T)
    (m : a ∈ rowVars (rowOfKey G k)) :
    ∃ p : PrivatePos V E T, a=.inl p ∧ originalClauseKey p=k := by
  cases k with
  | vertexSwitch v =>
    simp [rowVars,rowOfKey,switchRow,privateLit] at m
    rcases m with rfl|rfl <;> exact ⟨_,rfl,rfl⟩
  | edgeConflict e =>
    simp [rowVars,rowOfKey,conflictRow,privateLit] at m
    rcases m with rfl|rfl <;> exact ⟨_,rfl,rfl⟩
  | edgeRequest e =>
    simp [rowVars,rowOfKey,edgeRow,privateLit] at m
    rcases m with rfl|rfl|rfl <;> exact ⟨_,rfl,rfl⟩
  | tripleClause t i =>
    fin_cases i <;> simp [rowVars,rowOfKey,tripleRows,privateLit] at m
    · rcases m with rfl|rfl <;> exact ⟨_,rfl,rfl⟩
    · rcases m with rfl|rfl <;> exact ⟨_,rfl,rfl⟩
    · rcases m with rfl|rfl|rfl <;> exact ⟨_,rfl,rfl⟩
    · rcases m with rfl|rfl|rfl <;> exact ⟨_,rfl,rfl⟩

theorem same_owner_of_shared_base_slot (G : RequestGraph V E T)
    (k l : OriginalClauseKey V E T) (a : PhysicalVar V E T)
    (hk : a∈rowVars (rowOfKey G k)) (hl : a∈rowVars (rowOfKey G l)) : k=l := by
  obtain ⟨p,ap,kp⟩ := keyed_variable_belongs_to_owner G k a hk
  obtain ⟨q,aq,lq⟩ := keyed_variable_belongs_to_owner G l a hl
  have h : p=q := Sum.inl.inj (ap.symm.trans aq)
  exact kp.symm.trans ((congrArg originalClauseKey h).trans lq)

theorem rowOfKey_injective (G : RequestGraph V E T) : Function.Injective (rowOfKey G) := by
  intro k l eq
  have len : 0<(rowVars (rowOfKey G k)).length := by
    change 0<((rowOfKey G k).map _).length
    rw [List.length_map]
    exact (by decide : 0<2).trans_le (keyed_row_two_or_more G k)
  let a := (rowVars (rowOfKey G k))[0]'len
  have m : a∈rowVars (rowOfKey G k) := List.getElem_mem (h:=len)
  exact same_owner_of_shared_base_slot G k l a m (eq ▸ m)

theorem private_key_lists_once (v : Listing V) (e : Listing E) (t : Listing T) :
    (originalKeys v e t).Nodup := by
  unfold originalKeys
  have edgeOnce : (e.elems.flatMap (edgeKeys (V:=V) (T:=T))).Nodup := by
    apply List.nodup_flatMap.2
    refine ⟨fun _ _=>by simp [edgeKeys],e.once.imp ?_⟩
    intro a b ne z hm hn
    simp only [edgeKeys,List.mem_cons,List.not_mem_nil,or_false] at hm hn
    rcases hm with rfl|rfl <;> simp_all
  have tripleOnce : (t.elems.flatMap (tripleKeys (V:=V) (E:=E))).Nodup := by
    apply List.nodup_flatMap.2
    refine ⟨fun _ _=>by simp [tripleKeys],t.once.imp ?_⟩
    intro a b ne z hm hn
    simp only [tripleKeys,List.mem_cons,List.not_mem_nil,or_false] at hm hn
    rcases hm with rfl|rfl|rfl|rfl <;> simp_all
  refine List.Nodup.append (v.once.map (fun _ _ h => OriginalClauseKey.vertexSwitch.inj h)) ?_ ?_
  · refine List.Nodup.append edgeOnce tripleOnce ?_
    intro z h k
    obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp h
    obtain ⟨b,_,hb⟩ := List.mem_flatMap.mp k
    simp only [edgeKeys,tripleKeys,List.mem_cons,List.not_mem_nil,or_false] at ha hb
    rcases ha with rfl|rfl <;> simp_all
  · intro z h k
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp h
    rcases List.mem_append.mp k with k|k
    · obtain ⟨b,_,hb⟩ := List.mem_flatMap.mp k
      simp [edgeKeys] at hb
    · obtain ⟨b,_,hb⟩ := List.mem_flatMap.mp k
      simp [tripleKeys] at hb

theorem actual_base_rows_once (G : RequestGraph V E T)
    (v : Listing V) (e : Listing E) (t : Listing T) :
    (baseRows G v e t).Nodup := by
  rw [base_rows_are_keyed]
  exact (private_key_lists_once v e t).map (rowOfKey_injective G)

#print axioms base_rows_are_keyed
#print axioms keyed_row_width
#print axioms keyed_row_two_or_more
#print axioms keyed_variables_distinct
#print axioms keyed_variable_belongs_to_owner
#print axioms same_owner_of_shared_base_slot
#print axioms rowOfKey_injective
#print axioms private_key_lists_once
#print axioms actual_base_rows_once
end F5R62.Normalization
