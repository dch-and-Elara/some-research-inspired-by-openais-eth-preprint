import F5R63SparsifyIncidence
import Mathlib.Data.Finset.Card

/-! Exact source branching criterion for literal sets (MAIN 3647–3675).
The old emitted list is unchanged by normalization, not substituted by
an equisatisfiable formula. The Finset presentation represents the same
clause family, with its actual literal signs. -/
namespace F5R63.Sparsify
open F5R60 F5R61 F5R62.PhysicalEmit F5R62.Normalization
open scoped Classical
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

variable {V E T : Type}

def clauseSet (r : Row V E T) : Finset (Signed V E T) := r.toFinset

def clauseFamily (F : CNF V E T) : Finset (Finset (Signed V E T)) :=
  (F.map clauseSet).toFinset

theorem actual_signed_set_has_original_width {F : CNF V E T} (P : PrintedNoDeletion F)
    {r : Row V E T} (hr : r∈F) :
    (clauseSet r).card = r.length :=
  List.toFinset_card_of_nodup (P.noRepeatedLiteral r hr)

theorem actual_signed_sets_once {F : CNF V E T} (P : PrintedNoDeletion F) :
    (F.map clauseSet).Nodup := by
  apply P.rowsNodup.map_on
  intro r hr s hs eq
  apply P.supportAntichain r hr s hs
  apply signed_subset_implies_support_subset
  intro l ml
  have mem : l∈clauseSet r := List.mem_toFinset.mpr ml
  have other : l∈clauseSet s := by rw [← eq]; exact mem
  exact List.mem_toFinset.mp other

theorem actual_family_has_original_clause_count {F : CNF V E T} (P : PrintedNoDeletion F) :
    (clauseFamily F).card=F.length := by
  change ((F.map clauseSet).toFinset).card=_
  rw [List.toFinset_card_of_nodup (actual_signed_sets_once P),List.length_map]

/-- MAIN 3665: number of width-c clauses containing all the signed literals in H. -/
def degreeAtWidth (C : Finset (Finset (Signed V E T))) (c : ℕ) (H : Finset (Signed V E T)) : ℕ :=
  (C.filter (fun r => r.card=c ∧ H⊆r)).card

private def hits (c : ℕ) (H : Finset (Signed V E T)) (r : Finset (Signed V E T)) : Bool :=
  decide (r.card=c ∧ H⊆r)

theorem printed_degree_is_emitted_signed_row_count {F : CNF V E T} (P : PrintedNoDeletion F)
    (c : ℕ) (H : Finset (Signed V E T)) :
    degreeAtWidth (clauseFamily F) c H =
      F.countP (fun r => hits c H (clauseSet r)) := by
  let L := F.map clauseSet
  have m : (L.filter (hits c H)).toFinset =
      (clauseFamily F).filter (fun r => r.card=c ∧ H⊆r) := by
    ext r
    simp only [clauseFamily,← show L=F.map clauseSet from rfl,Finset.mem_filter,List.mem_toFinset,
      List.mem_filter,hits,decide_eq_true_eq]
  rw [degreeAtWidth,← m,List.toFinset_card_of_nodup ((actual_signed_sets_once P).filter _),
    ← List.countP_eq_length_filter,List.countP_map]
  rfl

private theorem countP_le_occurrence (F : CNF V E T) (p : Row V E T → Bool)
    (x : PhysicalVar V E T) (supported : ∀ r∈F, p r=true → x∈rowVars r) :
    F.countP p ≤ variableOccurrences F x := by
  induction F with
  | nil => simp [variableOccurrences,occupied]
  | cons r F ih =>
    have tail := ih (fun z hz => supported z (List.mem_cons_of_mem r hz))
    have split : variableOccurrences (r::F) x =
        variableOccurrences [r] x + variableOccurrences F x := occurrences_append [r] F x
    rw [split,List.countP_cons]
    by_cases h : p r=true
    · have found : x∈rowVars r := supported r List.mem_cons_self h
      have atLeast : 0 < variableOccurrences [r] x := by
        unfold variableOccurrences
        apply (eqCount_pos_iff x _).2
        exact List.mem_flatMap.mpr ⟨r,by simp,found⟩
      simp only [h,if_true]
      omega
    · have b : p r=false := by cases f : p r <;> simp_all
      simp [b]
      omega

theorem printed_degree_le_any_shared_physical_occurrence {F : CNF V E T}
    (P : PrintedNoDeletion F) (c : ℕ) (H : Finset (Signed V E T))
    (l : Signed V E T) (hl : l∈H) :
    degreeAtWidth (clauseFamily F) c H ≤ variableOccurrences F l.var := by
  rw [printed_degree_is_emitted_signed_row_count P]
  apply countP_le_occurrence
  intro r _ h
  have contained : H⊆clauseSet r := (of_decide_eq_true h).2
  exact List.mem_map_of_mem (List.mem_toFinset.mp (contained hl))

/-- Literal MAIN violation, with c supplied by the real containing
clause; strict inclusion is the source's proper-subset quantifier. -/
def printedViolation
    (C : Finset (Finset (Signed V E T))) (M : ℕ) : Prop :=
  ∃ A∈C, ∃ H : Finset (Signed V E T), H.Nonempty ∧ H ⊂ A ∧
    M^(A.card-H.card) ≤ degreeAtWidth C A.card H

theorem no_printed_violation_of_occurrences {F : CNF V E T} (P : PrintedNoDeletion F)
    (M : ℕ) (threshold : 4≤M) (occ : ∀ x,variableOccurrences F x≤3) :
    ¬printedViolation (clauseFamily F) M := by
  rintro ⟨A,_,H,nonempty,proper,viol⟩
  obtain ⟨l,hl⟩ := nonempty
  have gap : 1≤A.card-H.card := by
    have h := Finset.card_lt_card proper
    omega
  have minCost : M ≤ M^(A.card-H.card) := by
    have h : M^1 ≤ M^(A.card-H.card) := Nat.pow_le_pow_right (by omega) gap
    simpa only [pow_one] using h
  have bound : degreeAtWidth (clauseFamily F) A.card H≤3 :=
    (printed_degree_le_any_shared_physical_occurrence P A.card H l hl).trans (occ _)
  omega

/-- Identity of the root formula if there is no legal first branch.
Only the root decision is represented; children and the general
sparsifier are not implemented here. -/
def printedRootStop (F : CNF V E T) (M : ℕ) : Option (CNF V E T) :=
  if printedViolation (clauseFamily F) M then none else some F

structure PrintedUnchangedLeaf (F : CNF V E T) (M : ℕ) : Prop where
  noDeletion : PrintedNoDeletion F
  noBranch : ¬printedViolation (clauseFamily F) M
  identicalRoot : printedRootStop F M = some F

section Actual
variable [DecidableEq V] [DecidableEq T] [Fintype V] [Fintype E] [Fintype T]

theorem actual_F1_unchanged_leaf_at_threshold
    (G : RequestGraph V E T) (v : Listing V) (e : Listing E) (t : Listing T)
    (distinct : DistinctSourceEnds G) (incident : ∀ x, ∃ a, G.left a=x ∨ G.right a=x)
    (M : ℕ) (hM : 4≤M) :
    PrintedUnchangedLeaf (f1ActualCNF G v e t) M := by
  have normalization := actual_F1_source_normalization G v e t distinct incident
  have noBranch := no_printed_violation_of_occurrences normalization M hM
    (actual_F1_max_physical_occurrence_three G v e t)
  exact ⟨normalization,noBranch,if_neg noBranch⟩

end Actual

#print axioms actual_signed_set_has_original_width
#print axioms actual_signed_sets_once
#print axioms actual_family_has_original_clause_count
#print axioms printed_degree_is_emitted_signed_row_count
#print axioms printed_degree_le_any_shared_physical_occurrence
#print axioms no_printed_violation_of_occurrences
#print axioms actual_F1_unchanged_leaf_at_threshold
end
end F5R63.Sparsify