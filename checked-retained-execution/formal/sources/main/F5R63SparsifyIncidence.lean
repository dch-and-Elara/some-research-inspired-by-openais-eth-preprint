import F5R62NormalizationFinal
import Mathlib.Data.List.Count

/-! Original v8 §F1: every actual private physical slot is in one original
clause and in exactly two implication incidences, while each detached
variable occurs exactly once. We count the signed emitted list, ignoring
polarity only when taking the occurrence of a physical variable. -/
namespace F5R63.Sparsify
open F5R60 F5R61 F5R62.PhysicalEmit F5R62.Normalization
open scoped Classical
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
noncomputable section

variable {V E T : Type}

/-- Propositional equality is fixed once, avoiding a possibly non-lawful
specialized Boolean equality on a compound physical tag. -/
def eqCount {A : Type} (x : A) (L : List A) : ℕ :=
  letI : DecidableEq A := Classical.decEq A
  L.count x

theorem eqCount_append {A : Type} (x : A) (L K : List A) :
    eqCount x (L++K)=eqCount x L + eqCount x K := by
  letI : DecidableEq A := Classical.decEq A
  exact List.count_append

theorem eqCount_pos_iff {A : Type} (x : A) (L : List A) : 0 < eqCount x L ↔ x∈L := by
  letI : DecidableEq A := Classical.decEq A
  exact List.count_pos_iff

theorem eqCount_single {A : Type} (x z : A) : eqCount x [z]=(if z=x then 1 else 0) := by
  letI : DecidableEq A := Classical.decEq A
  change List.count x [z] = _
  by_cases h : z=x
  · simp [h]
  · simp [List.count_cons_of_ne h,h]

theorem eqCount_one_of_nodup_mem {A : Type} {x : A} {L : List A}
    (once : L.Nodup) (m : x∈L) : eqCount x L=1 := by
  letI : DecidableEq A := Classical.decEq A
  exact List.count_eq_one_of_mem once m

theorem eqCount_zero_of_not_mem {A : Type} {x : A} {L : List A}
    (m : x∉L) : eqCount x L=0 := by
  letI : DecidableEq A := Classical.decEq A
  exact List.count_eq_zero_of_not_mem m

@[simp] theorem eqCount_nil {A : Type} (x : A) : eqCount x []=0 := rfl

/-- The list of all actual incidences of the same signed CNF. -/
def occupied (F : CNF V E T) := F.flatMap rowVars

def variableOccurrences (F : CNF V E T) (x : PhysicalVar V E T) : ℕ :=
  eqCount x (occupied F)

theorem occurrences_append (A B : CNF V E T) (x : PhysicalVar V E T) :
    variableOccurrences (A++B) x = variableOccurrences A x + variableOccurrences B x := by
  simp [variableOccurrences,occupied,List.flatMap_append,eqCount_append]

theorem private_in_own_base_row (G : RequestGraph V E T) (p : PrivatePos V E T) :
    Sum.inl p ∈ rowVars (rowOfKey G (originalClauseKey p)) := by
  cases p with
  | sw u j =>
    fin_cases j <;> simp [rowVars,rowOfKey,originalClauseKey,switchRow,privateLit]
  | cf u j =>
    fin_cases j <;> simp [rowVars,rowOfKey,originalClauseKey,conflictRow,privateLit]
  | er u j =>
    fin_cases j <;> simp [rowVars,rowOfKey,originalClauseKey,edgeRow,privateLit]
  | tr u j =>
    fin_cases j <;>
      simp [rowVars,rowOfKey,originalClauseKey,tripleClausePart,tripleRows,privateLit]

theorem every_actual_base_key (v : Listing V) (e : Listing E) (t : Listing T)
    (k : OriginalClauseKey V E T) : k ∈ originalKeys v e t := by
  cases k with
  | vertexSwitch x =>
    exact List.mem_append_left _ (List.mem_map_of_mem (v.all x))
  | edgeConflict a =>
    exact List.mem_append_right _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨a,e.all a,by simp [edgeKeys]⟩))
  | edgeRequest a =>
    exact List.mem_append_right _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨a,e.all a,by simp [edgeKeys]⟩))
  | tripleClause d j =>
    exact List.mem_append_right _ (List.mem_append_right _
      (List.mem_flatMap.mpr ⟨d,t.all d,by fin_cases j <;> simp [tripleKeys]⟩))

theorem actual_base_occupied_once (G : RequestGraph V E T)
    (v : Listing V) (e : Listing E) (t : Listing T) :
    (occupied (baseRows G v e t)).Nodup ∧
      ∀ p : PrivatePos V E T, Sum.inl p ∈ occupied (baseRows G v e t) := by
  rw [base_rows_are_keyed]
  simp only [occupied,List.flatMap_map,Function.comp_def]
  constructor
  · apply List.nodup_flatMap.mpr
    exact ⟨fun k _ => keyed_variables_distinct G k,
      (private_key_lists_once v e t).imp (fun ne x hx hy =>
        ne (same_owner_of_shared_base_slot G _ _ x hx hy))⟩
  · intro p
    exact List.mem_flatMap.mpr ⟨originalClauseKey p,every_actual_base_key v e t _,
      private_in_own_base_row G p⟩

theorem actual_base_private_count (G : RequestGraph V E T)
    (v : Listing V) (e : Listing E) (t : Listing T) (p : PrivatePos V E T) :
    variableOccurrences (baseRows G v e t) (.inl p)=1 := by
  exact eqCount_one_of_nodup_mem (actual_base_occupied_once G v e t).1
    ((actual_base_occupied_once G v e t).2 p)

theorem actual_base_detached_count (G : RequestGraph V E T)
    (v : Listing V) (e : Listing E) (t : Listing T) (b : Bool) :
    variableOccurrences (baseRows G v e t) (.inr b)=0 := by
  apply eqCount_zero_of_not_mem
  rintro h
  obtain ⟨r,hr,m⟩ := List.mem_flatMap.mp h
  rw [base_rows_are_keyed] at hr
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hr
  exact keyed_support_contains_no_detached G k b m

private def names (xs : List (PrivatePos V E T)) : List (PhysicalVar V E T) :=
  xs.map Sum.inl

-- The missing closing source slot is made explicit, so induction follows
-- the very same rows that are emitted by the open implication chain.
private theorem chain_counts (x : PhysicalVar V E T)
    (p : PrivatePos V E T) (xs : List (PrivatePos V E T)) :
    variableOccurrences (chainRows p xs) x + eqCount x [Sum.inl (lastFrom p xs)] =
      eqCount x (names (p::xs)) + eqCount x (names xs) := by
  induction xs generalizing p with
  | nil => simp [chainRows,variableOccurrences,occupied,names,lastFrom]
  | cons q qs ih =>
    have step := ih q
    have node : variableOccurrences (chainRows p (q::qs)) x =
        eqCount x [Sum.inl p] + eqCount x [Sum.inl q] +
          variableOccurrences (chainRows q qs) x := by
      change variableOccurrences ([implicationRow p q]++chainRows q qs) x = _
      rw [occurrences_append]
      change eqCount x ([Sum.inl p] ++ [Sum.inl q]) + _ = _
      rw [eqCount_append]
    rw [node]
    have count_cons' (r : PrivatePos V E T) (rs : List (PrivatePos V E T)) :
        eqCount x (names (r::rs)) = eqCount x [Sum.inl r] + eqCount x (names rs) := by
      change eqCount x ([Sum.inl r]++names rs) = _
      exact eqCount_append _ _ _
    rw [count_cons' p, count_cons' q]
    rw [count_cons' q] at step
    change _ + eqCount x [Sum.inl (lastFrom q qs)] = _
    omega

theorem cycle_doubles_actual_slots (G : RequestGraph V E T) [DecidableEq V] [DecidableEq T]
    (v : Listing V) (e : Listing E) (t : Listing T)
    (n : Logical V T) (x : PhysicalVar V E T) :
    variableOccurrences (cycleRowsAt (generatedPrintedCycles G v e t) n) x =
      2*eqCount x (names (actualCycleList G v e t n)) := by
  let D := generatedPrintedCycles G v e t
  change variableOccurrences (cycleRowsAt D n) x = _
  have ord : D.first n :: D.rest n = actualCycleList G v e t n :=
    reconstruct_cycle_list G v e t n
  rw [← ord]
  have cnt := chain_counts x (D.first n) (D.rest n)
  have total : eqCount x (names (D.first n::D.rest n)) =
      eqCount x [Sum.inl (D.first n)] + eqCount x (names (D.rest n)) := by
    change eqCount x ([Sum.inl (D.first n)]++names (D.rest n)) = _
    exact eqCount_append _ _ _
  have closing : variableOccurrences [implicationRow (D.last n) (D.first n)] x =
      eqCount x [Sum.inl (lastFrom (D.first n) (D.rest n))] +
        eqCount x [Sum.inl (D.first n)] := by
    change eqCount x ([Sum.inl (lastFrom (D.first n) (D.rest n))] ++ [Sum.inl (D.first n)]) = _
    exact eqCount_append _ _ _
  rw [cycleRowsAt,occurrences_append,closing]
  omega
private theorem occurrences_flatMap {I : Type} (L : List I) (get : I→CNF V E T)
    (x : PhysicalVar V E T) :
    variableOccurrences (L.flatMap get) x =
      (L.map (fun i => variableOccurrences (get i) x)).sum := by
  induction L with
  | nil => rfl
  | cons a as ih => simp [List.flatMap_cons,occurrences_append,ih]

private def doubleHit {I : Type} (x i : I) : ℕ := if i=x then 2 else 0

private theorem sum_double_if_eq {I : Type} (L : List I) (x : I) :
    (L.map (doubleHit x)).sum = 2*eqCount x L := by
  induction L with
  | nil => rfl
  | cons a as ih =>
    change doubleHit x a + (List.map (doubleHit x) as).sum = 2*eqCount x ([a]++as)
    rw [ih,eqCount_append,eqCount_single]
    by_cases h : a=x
    · simp [doubleHit,h,Nat.mul_add,Nat.add_comm]
    · simp [doubleHit,h,Nat.mul_add]
section Whole
variable [DecidableEq V] [DecidableEq T] [Fintype V] [Fintype E] [Fintype T]
variable (G : RequestGraph V E T) (v : Listing V) (e : Listing E) (t : Listing T)

theorem actual_cycles_private_count (p : PrivatePos V E T) :
    variableOccurrences (cycleRows (generatedPrintedCycles G v e t) v t) (.inl p)=2 := by
  rw [cycleRows,occurrences_flatMap]
  have count_at (n : Logical V T) :
      variableOccurrences (cycleRowsAt (generatedPrintedCycles G v e t) n) (.inl p) =
        doubleHit (nameOf G p) n := by
    rw [cycle_doubles_actual_slots]
    have iffmem : (Sum.inl p : PhysicalVar V E T) ∈ names (actualCycleList G v e t n) ↔
        nameOf G p=n := by
      simp only [names,List.mem_map]
      constructor
      · rintro ⟨q,m,eq⟩
        exact (actualCycleList_exact_members G v e t p n).1 (Sum.inl.inj eq ▸ m)
      · intro h
        exact ⟨p,(actualCycleList_exact_members G v e t p n).2 h,rfl⟩
    by_cases h : n=nameOf G p
    · have one : eqCount (Sum.inl p : PhysicalVar V E T) (names (actualCycleList G v e t n))=1 := eqCount_one_of_nodup_mem
        ((actual_cycle_nodup G v e t n).map (fun _ _ eq => Sum.inl.inj eq))
        (iffmem.2 h.symm)
      simp only [doubleHit,if_pos h,one,Nat.mul_one]
    · have zero := eqCount_zero_of_not_mem (fun m => h (iffmem.1 m).symm)
      simp [doubleHit,h,zero]
  simp only [count_at,sum_double_if_eq,
    eqCount_one_of_nodup_mem (logicalListing v t).once ((logicalListing v t).all (nameOf G p)),
    Nat.mul_one]
theorem actual_cycles_detached_count (b : Bool) :
    variableOccurrences (cycleRows (generatedPrintedCycles G v e t) v t) (.inr b)=0 := by
  apply eqCount_zero_of_not_mem
  intro m
  obtain ⟨r,hm,where_⟩ := List.mem_flatMap.mp m
  exact emitted_cycle_support_no_detached G v e t r hm b where_

theorem every_actual_private_slot_occurs_three_times (p : PrivatePos V E T) :
    variableOccurrences (f1ActualCNF G v e t) (.inl p)=3 := by
  rw [f1ActualCNF,occurrences_append,occurrences_append,
    actual_base_private_count,actual_cycles_private_count]
  rw [show variableOccurrences [detachedRow] (.inl p)=0 from
    eqCount_zero_of_not_mem (by simp [occupied,rowVars,detachedRow,detachedLit])]

theorem actual_detached_each_occurs_once (b : Bool) :
    variableOccurrences (f1ActualCNF G v e t) (.inr b)=1 := by
  rw [f1ActualCNF,occurrences_append,occurrences_append,
    actual_base_detached_count,actual_cycles_detached_count]
  change 0+(0+eqCount (Sum.inr b) ([Sum.inr false]++[Sum.inr true]))=1
  rw [eqCount_append,eqCount_single,eqCount_single]
  cases b <;> simp

theorem actual_F1_max_physical_occurrence_three (x : PhysicalVar V E T) :
    variableOccurrences (f1ActualCNF G v e t) x ≤ 3 := by
  cases x with
  | inl p => rw [every_actual_private_slot_occurs_three_times]
  | inr b => rw [actual_detached_each_occurs_once]; decide

end Whole

#print axioms eqCount_append
#print axioms eqCount_pos_iff
#print axioms eqCount_single
#print axioms eqCount_one_of_nodup_mem
#print axioms eqCount_zero_of_not_mem
#print axioms occurrences_append
#print axioms private_in_own_base_row
#print axioms every_actual_base_key
#print axioms actual_base_occupied_once
#print axioms actual_base_private_count
#print axioms actual_base_detached_count
#print axioms cycle_doubles_actual_slots
#print axioms actual_cycles_private_count
#print axioms actual_cycles_detached_count
#print axioms every_actual_private_slot_occurs_three_times
#print axioms actual_detached_each_occurs_once
#print axioms actual_F1_max_physical_occurrence_three
end
end F5R63.Sparsify