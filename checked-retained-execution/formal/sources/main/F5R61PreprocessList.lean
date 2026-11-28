import F5R61Preprocess
import Mathlib.Data.List.Nodup

/-! Literal list materialization of the exact first F5 CNF. The output
walks the true clause ranks first, then the active occurrence ranks,
and emits the actual signed list of literals for each visited row. -/
namespace F5R61.Preprocess
set_option autoImplicit false
set_option warningAsError true
open F5R59

variable {V : Type} {m n : ℕ} [DecidableEq V]
variable (S : ClauseSystem (Fin m) V) (e : Fin n ≃ Vertex S)

def activeClauseAt (i : Fin n) : Option (EmittedClause S e) :=
  if h : active S e (e i) then some (.inr ⟨e i,h⟩) else none

theorem selected_active_clause_at (i : Fin n) (row : EmittedClause S e)
    (h : activeClauseAt S e i = some row) :
    ∃ a : active S e (e i), row=.inr ⟨e i,a⟩ := by
  unfold activeClauseAt at h
  split at h
  · rename_i a
    exact ⟨a,(Option.some.inj h).symm⟩
  · contradiction

def orderedClauses : List (EmittedClause S e) :=
  (List.finRange m).map Sum.inl ++ (List.finRange n).filterMap (activeClauseAt S e)

theorem every_emitted_clause_visited (c : EmittedClause S e) :
    c ∈ orderedClauses S e := by
  cases c with
  | inl c =>
    exact List.mem_append_left _ (List.mem_map.mpr ⟨c,List.mem_finRange c,rfl⟩)
  | inr x =>
    apply List.mem_append_right _
    apply List.mem_filterMap.mpr
    let i := e.symm x.val
    have eq : e i=x.val := e.apply_symm_apply x.val
    have h : active S e (e i) := by rw [eq]; exact x.property
    refine ⟨i,List.mem_finRange i,?_⟩
    rw [activeClauseAt,dif_pos h]
    have same : (⟨e i,h⟩ : {x : Vertex S // active S e x}) = x := Subtype.ext eq
    exact congrArg (fun y => (some (Sum.inr y) : Option (EmittedClause S e))) same

theorem emitted_clause_visit_unique : (orderedClauses S e).Nodup := by
  apply List.Nodup.append
  · exact (List.nodup_finRange m).map (fun _ _ eq => Sum.inl.inj eq)
  · refine List.Nodup.filterMap (fun a b c ha hb => ?_) (List.nodup_finRange n)
    obtain ⟨_,ha⟩ := selected_active_clause_at S e a c ha
    obtain ⟨_,hb⟩ := selected_active_clause_at S e b c hb
    exact e.injective (congrArg Subtype.val (Sum.inr.inj (ha.symm.trans hb)))
  · intro c hOrig hNew
    obtain ⟨_,_,eq⟩ := List.mem_map.mp hOrig
    obtain ⟨i,_,hi⟩ := List.mem_filterMap.mp hNew
    obtain ⟨_,hClause⟩ := selected_active_clause_at S e i c hi
    exact Sum.noConfusion (eq.trans hClause)

def actualClauseList (c : EmittedClause S e) : List (Literal (Vertex S)) :=
  List.ofFn ((copied S e).literal c)

def actualCNFList : List (List (Literal (Vertex S))) :=
  (orderedClauses S e).map (actualClauseList S e)

theorem actual_clause_list_has_exact_width (c : EmittedClause S e) :
    (actualClauseList S e c).length=(copied S e).width c :=
  List.length_ofFn

def ListSatisfied (R : List (List (Literal (Vertex S)))) (b : Vertex S → Bool) : Prop :=
  ∀ row ∈ R, ∃ t ∈ row, b t.var=t.positive

theorem actual_cnf_list_satisfies_iff (b : Vertex S → Bool) :
    ListSatisfied S (actualCNFList S e) b ↔ satisfies (copied S e) b := by
  constructor
  · intro h c
    have r : actualClauseList S e c ∈ actualCNFList S e :=
      List.mem_map.mpr ⟨c,every_emitted_clause_visited S e c,rfl⟩
    obtain ⟨t,ml,ht⟩ := h _ r
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ml
    exact ⟨i,ht⟩
  · intro h row hr
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hr
    obtain ⟨i,hi⟩ := h c
    exact ⟨_,List.mem_ofFn.mpr ⟨i,rfl⟩,hi⟩

theorem literal_list_compiled_width_three_sat_iff (width : ∀ c, S.width c=3) :
    (∃ b, ListSatisfied S (actualCNFList S (initialOrder S width)) b) ↔
      ∃ a, satisfies S a := by
  exact (exists_congr (actual_cnf_list_satisfies_iff S (initialOrder S width))).trans
    (copied_satisfiable_iff S (initialOrder S width))

#print axioms orderedClauses
#print axioms every_emitted_clause_visited
#print axioms emitted_clause_visit_unique
#print axioms actualCNFList
#print axioms actual_clause_list_has_exact_width
#print axioms actual_cnf_list_satisfies_iff
#print axioms literal_list_compiled_width_three_sat_iff
end F5R61.Preprocess
