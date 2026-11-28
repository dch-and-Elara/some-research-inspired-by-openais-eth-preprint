import F5R62NormalizationSeparation
import Mathlib.Tactic

/-! The actual emitted F1 clauses have incomparable physical supports.
This is stronger than incomparability of signed literal sets, which
is the original MAIN subsumption criterion. -/
namespace F5R62.Normalization
open F5R60 F5R61 F5R62.PhysicalEmit
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {V E T : Type}

theorem signed_subset_implies_support_subset (r s : Row V E T)
    (h : r ⊆ s) : rowVars r ⊆ rowVars s := by
  intro a ha
  obtain ⟨l,m,e⟩ := List.mem_map.mp ha
  exact List.mem_map.mpr ⟨l,h m,e⟩

private theorem support_member (r : Row V E T) (len : 0<r.length) :
    ∃ a, a∈rowVars r := by
  have h : 0<(rowVars r).length := by simpa only [rowVars,List.length_map] using len
  exact ⟨(rowVars r)[0]'h,List.getElem_mem (h:=h)⟩

private theorem both_of_two_distinct_subset_pair {A : Type}
    (r : List A) (len : 2≤r.length) (nodup : r.Nodup) {a b : A}
    (sub : r ⊆ [a,b]) : a∈r ∧ b∈r := by
  cases r with
  | nil => simp at len
  | cons u rest =>
    cases rest with
    | nil => simp at len
    | cons w xs =>
      have uh : u∈u::w::xs := List.mem_cons_self
      have wh : w∈u::w::xs := List.mem_cons_of_mem _ List.mem_cons_self
      have dw : u≠w := fun eq => (List.nodup_cons.mp nodup).1 (by rw [eq]; exact List.mem_cons_self)
      have up : u=a ∨ u=b := by simpa using sub uh
      have wp : w=a ∨ w=b := by simpa using sub wh
      rcases up with up|up <;> rcases wp with wp|wp <;> simp_all

theorem detached_support_contains_no_private (p : PrivatePos V E T) :
    Sum.inl p∉rowVars (detachedRow (V:=V) (E:=E) (T:=T)) := by
  simp [rowVars,detachedRow,detachedLit]

theorem detached_seat_on_actual_detached_row :
    Sum.inr false∈rowVars (detachedRow (V:=V) (E:=E) (T:=T)) := by
  simp [rowVars,detachedRow,detachedLit]

theorem keyed_support_contains_no_detached (G : RequestGraph V E T)
    (k : OriginalClauseKey V E T) (a : Bool) :
    Sum.inr a∉rowVars (rowOfKey G k) := by
  intro hm
  obtain ⟨p,e,_⟩ := keyed_variable_belongs_to_owner G k _ hm
  cases e

section Cycles
variable [DecidableEq V] [DecidableEq T] [Fintype V] [Fintype E] [Fintype T]
variable (G : RequestGraph V E T) (v : Listing V) (e : Listing E) (t : Listing T)
variable (incident : ∀ x, ∃ a, G.left a=x ∨ G.right a=x)

theorem emitted_cycle_support_no_detached (r : Row V E T)
    (h : r∈cycleRows (generatedPrintedCycles G v e t) v t) (a : Bool) :
    Sum.inr a∉rowVars r := by
  obtain ⟨n,p,q,i,j,rfl,_ip,_iq,_step⟩ := actual_emission_is_circular_step G v e t r h
  simp [rowVars,implicationRow,privateLit]

theorem emitted_cycle_has_private_support (r : Row V E T)
    (h : r∈cycleRows (generatedPrintedCycles G v e t) v t) :
    ∃ p : PrivatePos V E T, Sum.inl p∈rowVars r := by
  obtain ⟨n,p,q,i,j,rfl,_ip,_iq,_step⟩ := actual_emission_is_circular_step G v e t r h
  exact ⟨p,by simp [rowVars,implicationRow,privateLit]⟩

include incident in
theorem emitted_cycle_unordered_support_subset_eq (r s : Row V E T)
    (hr : r∈cycleRows (generatedPrintedCycles G v e t) v t)
    (hs : s∈cycleRows (generatedPrintedCycles G v e t) v t)
    (sub : rowVars r ⊆ rowVars s) : r=s := by
  obtain ⟨n,p,q,i,j,rfl,ip,jq,st⟩ := actual_emission_is_circular_step G v e t r hr
  obtain ⟨m,p',q',k,l,rfl,kp,lq,st'⟩ := actual_emission_is_circular_step G v e t s hs
  obtain ⟨ne,np,nq⟩ := source_step_distinct_names G v e t incident n p q i j ip jq st
  obtain ⟨_ne',mp,mq⟩ := source_step_distinct_names G v e t incident m p' q' k l kp lq st'
  have left : p=p' ∨ p=q' := by
    have h : Sum.inl p∈rowVars (implicationRow p' q') :=
      sub (by simp [rowVars,implicationRow,privateLit])
    simpa [rowVars,implicationRow,privateLit] using h
  have right : q=p' ∨ q=q' := by
    have h : Sum.inl q∈rowVars (implicationRow p' q') :=
      sub (by simp [rowVars,implicationRow,privateLit])
    simpa [rowVars,implicationRow,privateLit] using h
  rcases left with a|a <;> rcases right with b|b
  · exact False.elim (ne (a.trans b.symm))
  · rw [a,b]
  · exfalso
    have same : n=m := np.symm.trans ((congrArg (nameOf G) a).trans mq)
    rw [← same] at kp lq st'
    have eqi : (actualCycleList G v e t n)[i]?=(actualCycleList G v e t n)[l]? := by rw [ip,lq,a]
    have eqj : (actualCycleList G v e t n)[j]?=(actualCycleList G v e t n)[k]? := by rw [jq,kp,b]
    have hi := (List.getElem?_eq_some_iff.mp ip).1
    have hj := (List.getElem?_eq_some_iff.mp jq).1
    have once := actual_cycle_nodup G v e t n
    have si := List.getElem?_inj hi once eqi
    have sj := List.getElem?_inj hj once eqj
    have len := each_actual_cycle_has_four G v e t incident n
    rcases st with u | ⟨u,u0⟩ <;> rcases st' with w | ⟨w,w0⟩ <;> omega
  · exact False.elim (ne (a.trans b.symm))

include incident in
theorem keyed_support_not_inside_cycle
    (distinct : DistinctSourceEnds G) (k : OriginalClauseKey V E T)
    (r : Row V E T) (hr : r∈cycleRows (generatedPrintedCycles G v e t) v t) :
    ¬ rowVars (rowOfKey G k) ⊆ rowVars r := by
  intro contained
  obtain ⟨p,q,shape,_hne,_same⟩ := emitted_implication_two_distinct_private G v e t incident r hr
  have fit : 2≤(rowVars (rowOfKey G k)).length := by
    simpa only [rowVars,List.length_map] using keyed_row_two_or_more G k
  have cp : rowVars (rowOfKey G k) ⊆ [Sum.inl p,Sum.inl q] := by
    simpa [shape,rowVars,implicationRow,privateLit] using contained
  obtain ⟨a,b⟩ := both_of_two_distinct_subset_pair _ fit (keyed_variables_distinct G k) cp
  apply emitted_implication_not_in_any_original G v e t distinct incident r hr k
  intro y hy
  have yz : y=.inl p ∨ y=.inl q := by simpa [shape,rowVars,implicationRow,privateLit] using hy
  rcases yz with rfl|rfl
  · exact a
  · exact b
end Cycles

section Whole
variable [DecidableEq V] [DecidableEq T]
variable (G : RequestGraph V E T) (v : Listing V) (e : Listing E) (t : Listing T)

theorem actual_F1_emitted_row_cases (r : Row V E T) (m : r∈f1ActualCNF G v e t) :
    (∃ k, r=rowOfKey G k) ∨
      r∈cycleRows (generatedPrintedCycles G v e t) v t ∨ r=detachedRow := by
  rw [f1ActualCNF,List.mem_append,List.mem_append] at m
  rcases m with inBase|inImp|inDet
  · rw [base_rows_are_keyed] at inBase
    obtain ⟨k,_,ke⟩ := List.mem_map.mp inBase
    exact Or.inl ⟨k,ke.symm⟩
  · exact Or.inr (Or.inl inImp)
  · exact Or.inr (Or.inr (List.mem_singleton.mp inDet))

variable [Fintype V] [Fintype E] [Fintype T]
variable (distinct : DistinctSourceEnds G) (incident : ∀ x, ∃ a, G.left a=x ∨ G.right a=x)

include distinct incident in
theorem actual_F1_support_antichain (r s : Row V E T) (hr : r∈f1ActualCNF G v e t)
    (hs : s∈f1ActualCNF G v e t) (h : rowVars r ⊆ rowVars s) : r=s := by
  have kr := actual_F1_emitted_row_cases G v e t r hr
  have ks := actual_F1_emitted_row_cases G v e t s hs
  rcases kr with ⟨k,rfl⟩ | hr' | rfl
  · rcases ks with ⟨l,rfl⟩ | hs' | rfl
    · obtain ⟨a,hm⟩ := support_member (rowOfKey G k)
        ((by decide : 0<2).trans_le (keyed_row_two_or_more G k))
      exact congrArg (rowOfKey G) (same_owner_of_shared_base_slot G k l a hm (h hm))
    · exact False.elim (keyed_support_not_inside_cycle G v e t incident distinct k s hs' h)
    · obtain ⟨a,hm⟩ := support_member (rowOfKey G k)
        ((by decide : 0<2).trans_le (keyed_row_two_or_more G k))
      obtain ⟨p,rfl,_⟩ := keyed_variable_belongs_to_owner G k a hm
      exact False.elim (detached_support_contains_no_private p (h hm))
  · rcases ks with ⟨k,rfl⟩ | hs' | rfl
    · exact False.elim (emitted_implication_not_in_any_original G v e t distinct incident r hr' k h)
    · exact emitted_cycle_unordered_support_subset_eq G v e t incident r s hr' hs' h
    · obtain ⟨p,hm⟩ := emitted_cycle_has_private_support G v e t r hr'
      exact False.elim (detached_support_contains_no_private p (h hm))
  · rcases ks with ⟨k,rfl⟩ | hs' | rfl
    · exact False.elim (keyed_support_contains_no_detached G k false
        (h detached_seat_on_actual_detached_row))
    · exact False.elim (emitted_cycle_support_no_detached G v e t s hs' false
        (h detached_seat_on_actual_detached_row))
    · rfl

include distinct incident in
theorem actual_F1_rows_have_no_duplicates : (f1ActualCNF G v e t).Nodup := by
  rw [f1ActualCNF]
  apply List.Nodup.append (actual_base_rows_once G v e t)
  · refine List.Nodup.append (actual_cycles_emit_no_duplicate_rows G v e t) (by simp) ?_
    intro r hc hd
    have eq : r=detachedRow := List.mem_singleton.mp hd
    exact emitted_cycle_support_no_detached G v e t r hc false (eq.symm ▸ detached_seat_on_actual_detached_row)
  · intro r hb hrest
    rcases List.mem_append.mp hrest with hc | hd
    · apply emitted_implication_not_in_any_base_row G v e t distinct incident r r hc hb
      intro _ hh
      exact hh
    · have eq : r=detachedRow := List.mem_singleton.mp hd
      rw [base_rows_are_keyed] at hb
      obtain ⟨k,_,row⟩ := List.mem_map.mp hb
      apply keyed_support_contains_no_detached G k false
      have eq' := row.trans eq
      exact eq'.symm ▸ detached_seat_on_actual_detached_row

include incident in
theorem actual_F1_row_width_and_distinct (r : Row V E T) (m : r∈f1ActualCNF G v e t) :
    (r.length=2 ∨ r.length=3) ∧ (rowVars r).Nodup := by
  rcases actual_F1_emitted_row_cases G v e t r m with ⟨k,rfl⟩|cyc|rfl
  · exact ⟨keyed_row_width G k,keyed_variables_distinct G k⟩
  · obtain ⟨p,q,rfl,ne,_same⟩ := emitted_implication_two_distinct_private G v e t incident r cyc
    exact ⟨Or.inl rfl,by simp [rowVars,implicationRow,privateLit,ne]⟩
  · exact ⟨Or.inl rfl,by simp [rowVars,detachedRow,detachedLit]⟩
end Whole

#print axioms signed_subset_implies_support_subset
#print axioms detached_support_contains_no_private
#print axioms keyed_support_contains_no_detached
#print axioms emitted_cycle_support_no_detached
#print axioms emitted_cycle_has_private_support
#print axioms emitted_cycle_unordered_support_subset_eq
#print axioms keyed_support_not_inside_cycle
#print axioms actual_F1_emitted_row_cases
#print axioms actual_F1_support_antichain
#print axioms actual_F1_rows_have_no_duplicates
#print axioms actual_F1_row_width_and_distinct
end F5R62.Normalization
