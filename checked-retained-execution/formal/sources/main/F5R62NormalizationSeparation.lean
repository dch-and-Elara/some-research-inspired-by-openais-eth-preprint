import F5R62NormalizationCycle

/-! The same two ends of a printed implication cannot be in the
same original physical clause. The argument uses the actual circular
order, not a supplied clause-antichain premise. -/
namespace F5R62.Normalization
open F5R60 F5R61 F5R62.PhysicalEmit
set_option autoImplicit false
set_option linter.unusedSimpArgs false
variable {V E T : Type} [DecidableEq V] [DecidableEq T] [Fintype V] [Fintype E] [Fintype T]
variable (G : RequestGraph V E T) (v : Listing V) (e : Listing E) (t : Listing T)

theorem emitted_implication_two_distinct_private
    (incident : ∀ x, ∃ a, G.left a=x ∨ G.right a=x) (r : Row V E T)
    (mem : r∈cycleRows (generatedPrintedCycles G v e t) v t) :
    ∃ p q : PrivatePos V E T, r=implicationRow p q ∧ p≠q ∧ nameOf G p=nameOf G q := by
  obtain ⟨n,p,q,i,j,eq,ip,jq,step⟩ := actual_emission_is_circular_step G v e t r mem
  obtain ⟨ne,hp,hq⟩ := source_step_distinct_names G v e t incident n p q i j ip jq step
  exact ⟨p,q,eq,ne,hp.trans hq.symm⟩

theorem emitted_implication_not_in_any_original
    (distinct : DistinctSourceEnds G) (incident : ∀ x, ∃ a, G.left a=x ∨ G.right a=x)
    (r : Row V E T) (mem : r∈cycleRows (generatedPrintedCycles G v e t) v t)
    (k : OriginalClauseKey V E T) :
    ¬ rowVars r ⊆ rowVars (rowOfKey G k) := by
  intro sub
  obtain ⟨n,p,q,i,j,rp,ip,jq,step⟩ := actual_emission_is_circular_step G v e t r mem
  obtain ⟨ne,np,nq⟩ := source_step_distinct_names G v e t incident n p q i j ip jq step
  have left : Sum.inl p∈rowVars (rowOfKey G k) :=
    sub (by simp [rp,rowVars,implicationRow,privateLit])
  have right : Sum.inl q∈rowVars (rowOfKey G k) :=
    sub (by simp [rp,rowVars,implicationRow,privateLit])
  obtain ⟨pf,eqp,kp⟩ := keyed_variable_belongs_to_owner G k _ left
  obtain ⟨qf,eqq,kq⟩ := keyed_variable_belongs_to_owner G k _ right
  have ep := Sum.inl.inj eqp
  have eq := Sum.inl.inj eqq
  subst pf
  subst qf
  have repeats : RepeatInOriginalClause G p q := ⟨np.trans nq.symm,kp.trans kq.symm,ne⟩
  have separated := generated_original_repeats_are_not_neighbours G distinct incident
    v e t n p q repeats i j ip jq
  exact separated.1 step

theorem emitted_implication_not_in_any_base_row
    (distinct : DistinctSourceEnds G) (incident : ∀ x, ∃ a, G.left a=x ∨ G.right a=x)
    (r b : Row V E T) (hr : r∈cycleRows (generatedPrintedCycles G v e t) v t)
    (hb : b∈baseRows G v e t) :
    ¬ rowVars r ⊆ rowVars b := by
  rw [base_rows_are_keyed] at hb
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hb
  exact emitted_implication_not_in_any_original G v e t distinct incident r hr k

#print axioms emitted_implication_two_distinct_private
#print axioms emitted_implication_not_in_any_original
#print axioms emitted_implication_not_in_any_base_row
end F5R62.Normalization
