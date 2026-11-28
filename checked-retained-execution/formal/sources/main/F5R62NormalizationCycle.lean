import F5R62PhysicalEmit
import F5R61ActualNoAdj
import F5R62NormalizationBase

/-! Decode an actually emitted implication row to the same generated
cyclic list, including the closing last-to-first step. -/
namespace F5R62.Normalization
open F5R60 F5R61 F5R62.PhysicalEmit
set_option autoImplicit false
set_option linter.unusedSimpArgs false
variable {V E T : Type}

theorem chain_emission_is_local_step (h : PrivatePos V E T) (xs : List (PrivatePos V E T))
    (r : Row V E T) (mem : r ∈ chainRows h xs) :
    ∃ (p q : PrivatePos V E T) (i : ℕ),
      r=implicationRow p q ∧ (h::xs)[i]?=some p ∧ (h::xs)[i+1]?=some q := by
  induction xs generalizing h with
  | nil =>
    simp [chainRows] at mem
  | cons a xs ih =>
    change r ∈ implicationRow h a :: chainRows a xs at mem
    rcases List.mem_cons.mp mem with here | later
    · exact ⟨h,a,0,here,rfl,rfl⟩
    · obtain ⟨p,q,i,eq,ip,iq⟩ := ih a later
      exact ⟨p,q,i+1,eq,by simpa using ip,by simpa using iq⟩

theorem lastFrom_at_real_last_index {P : Type} (p : P) (xs : List P) :
    (p::xs)[xs.length]? = some (lastFrom p xs) := by
  induction xs generalizing p with
  | nil => rfl
  | cons q xs ih =>
    change (q::xs)[xs.length]? = some (lastFrom q xs)
    exact ih q

variable [DecidableEq V] [DecidableEq T]
variable (G : RequestGraph V E T) (v : Listing V) (e : Listing E) (t : Listing T)

theorem actual_emission_is_circular_step (r : Row V E T)
    (mem : r ∈ cycleRows (generatedPrintedCycles G v e t) v t) :
    ∃ (n : Logical V T) (p q : PrivatePos V E T) (i j : ℕ),
      r=implicationRow p q ∧
      (actualCycleList G v e t n)[i]?=some p ∧ (actualCycleList G v e t n)[j]?=some q ∧
      nextIndex (actualCycleList G v e t n).length i j := by
  let D := generatedPrintedCycles G v e t
  have m : r ∈ (logicalListing v t).elems.flatMap (cycleRowsAt D) := mem
  obtain ⟨n,_mn,here⟩ := List.mem_flatMap.mp m
  have shape : D.first n :: D.rest n = actualCycleList G v e t n :=
    reconstruct_cycle_list G v e t n
  change r ∈ chainRows (D.first n) (D.rest n) ++ [implicationRow (D.last n) (D.first n)] at here
  rcases List.mem_append.mp here with inside | finish
  · obtain ⟨p,q,i,eq,ip,iq⟩ := chain_emission_is_local_step _ _ r inside
    exact ⟨n,p,q,i,i+1,eq,shape ▸ ip,shape ▸ iq,Or.inl rfl⟩
  · have hr : r=implicationRow (D.last n) (D.first n) := List.mem_singleton.mp finish
    have lastAt : (D.first n::D.rest n)[(D.rest n).length]?=some (D.last n) :=
      lastFrom_at_real_last_index _ _
    have firstAt : (D.first n::D.rest n)[0]?=some (D.first n) := rfl
    refine ⟨n,D.last n,D.first n,(D.rest n).length,0,hr,shape ▸ lastAt,shape ▸ firstAt,?_⟩
    exact Or.inr ⟨by rw [← shape]; rfl,rfl⟩

theorem source_step_distinct_names [Fintype V] [Fintype E] [Fintype T]
    (incident : ∀ x, ∃ a, G.left a=x ∨ G.right a=x)
    (n : Logical V T) (p q : PrivatePos V E T) (i j : ℕ)
    (ip : (actualCycleList G v e t n)[i]?=some p)
    (jq : (actualCycleList G v e t n)[j]?=some q)
    (step : nextIndex (actualCycleList G v e t n).length i j) :
    p≠q ∧ nameOf G p=n ∧ nameOf G q=n := by
  obtain ⟨hi,ei⟩ := List.getElem?_eq_some_iff.mp ip
  obtain ⟨hj,ej⟩ := List.getElem?_eq_some_iff.mp jq
  refine ⟨?_,(actualCycleList_exact_members G v e t p n).1 (List.mem_iff_getElem.2 ⟨i,hi,ei⟩),
    (actualCycleList_exact_members G v e t q n).1 (List.mem_iff_getElem.2 ⟨j,hj,ej⟩)⟩
  intro same
  have hsame : (actualCycleList G v e t n)[i]? = (actualCycleList G v e t n)[j]? := by
    rw [ip,jq,same]
  have sameIdx := List.getElem?_inj hi (actual_cycle_nodup G v e t n) hsame
  have length := each_actual_cycle_has_four G v e t incident n
  rcases step with hs | ⟨hs,ht⟩ <;> omega

def leadingVariable (r : Row V E T) : Option (PhysicalVar V E T) :=
  r.head?.map F5R59.Literal.var

omit [DecidableEq V] [DecidableEq T] in
theorem chain_starts_once (p : PrivatePos V E T) (xs : List (PrivatePos V E T)) :
    (chainRows p xs).map leadingVariable ++ [some (.inl (lastFrom p xs))] =
      (p::xs).map (fun z => some (.inl z : PhysicalVar V E T)) := by
  induction xs generalizing p with
  | nil => rfl
  | cons a xs ih =>
    change some (.inl p) ::
      ((chainRows a xs).map leadingVariable ++ [some (.inl (lastFrom a xs))]) = _
    rw [ih a]
    rfl

theorem actual_cycle_starts_once (n : Logical V T) :
    (cycleRowsAt (generatedPrintedCycles G v e t) n).map leadingVariable =
      (actualCycleList G v e t n).map (fun z => some (.inl z : PhysicalVar V E T)) := by
  let D := generatedPrintedCycles G v e t
  change (cycleRowsAt D n).map leadingVariable = _
  rw [← reconstruct_cycle_list G v e t n]
  rw [cycleRowsAt,List.map_append]
  exact chain_starts_once (D.first n) (D.rest n)

theorem actual_cycles_emit_no_duplicate_rows [Fintype V] [Fintype E] [Fintype T] :
    (cycleRows (generatedPrintedCycles G v e t) v t).Nodup := by
  let D := generatedPrintedCycles G v e t
  change ((logicalListing v t).elems.flatMap (cycleRowsAt D)).Nodup
  apply List.nodup_flatMap.2
  have enc : Function.Injective (fun z : PrivatePos V E T => some (.inl z : PhysicalVar V E T)) :=
    fun _ _ h => Sum.inl.inj (Option.some.inj h)
  refine ⟨fun n _ => List.Nodup.of_map leadingVariable ?_,(logicalListing v t).once.imp ?_⟩
  · rw [actual_cycle_starts_once]
    exact (actual_cycle_nodup G v e t n).map enc
  · intro n m hn r hr hs
    have left : leadingVariable r∈(cycleRowsAt D n).map leadingVariable := List.mem_map_of_mem hr
    have right : leadingVariable r∈(cycleRowsAt D m).map leadingVariable := List.mem_map_of_mem hs
    rw [actual_cycle_starts_once] at left right
    obtain ⟨p,hp,lp⟩ := List.mem_map.mp left
    obtain ⟨q,hq,rq⟩ := List.mem_map.mp right
    have eq : p=q := enc (lp.trans rq.symm)
    have nx := (actualCycleList_exact_members G v e t p n).1 hp
    have mx := (actualCycleList_exact_members G v e t q m).1 hq
    exact hn (nx.symm.trans ((congrArg (nameOf G) eq).trans mx))

#print axioms chain_emission_is_local_step
#print axioms lastFrom_at_real_last_index
#print axioms actual_emission_is_circular_step
#print axioms source_step_distinct_names
#print axioms chain_starts_once
#print axioms actual_cycle_starts_once
#print axioms actual_cycles_emit_no_duplicate_rows
end F5R62.Normalization
