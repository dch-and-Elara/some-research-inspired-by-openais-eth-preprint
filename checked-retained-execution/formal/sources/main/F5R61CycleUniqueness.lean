import F5R61RawSlots

namespace F5R61
open F5R60
set_option autoImplicit false
set_option linter.unusedSimpArgs false

theorem orderedSlots_perm {P : Type} (ps : List (P × P)) (extra : List P) :
    (orderedSlots ps extra).Perm (((ps.map Prod.fst) ++ ps.map Prod.snd) ++ extra) := by
  cases ps with
  | nil => exact List.Perm.refl _
  | cons p rest =>
    cases rest with
    | nil =>
      cases extra with
      | nil => exact List.Perm.refl _
      | cons u us =>
        cases us with
        | nil => exact List.Perm.refl _
        | cons v tail =>
          exact List.Perm.cons p.1 (List.Perm.swap p.2 u (v::tail))
    | cons p rest => simp [orderedSlots,List.append_assoc]

variable {V E T : Type} [DecidableEq V] [DecidableEq T]
variable (G : RequestGraph V E T) (v : Listing V) (e : Listing E) (t : Listing T)

theorem actual_fibre_raw_is_filter (n : Logical V T) :
    ((pairsOf G v e t n).map Prod.fst ++ (pairsOf G v e t n).map Prod.snd) ++ singlesOf G e t n =
      (rawSourceSlots v e t).filter (fun p => decide (nameOf G p = n)) := by
  rw [rawSourceSlots,List.filter_append,List.filter_append]
  simp only [List.filter_map,pairsOf,singlesOf,Function.comp_def]
  congr 2
  apply congrArg (List.map Prod.snd)
  apply List.filter_congr
  intro p mem
  rw [each_pair_has_same_logical_name G v e t p mem]

theorem actual_cycle_nodup [Fintype V] [Fintype E] [Fintype T] (n : Logical V T) :
    (actualCycleList G v e t n).Nodup := by
  apply (orderedSlots_perm (pairsOf G v e t n) (singlesOf G e t n)).nodup_iff.2
  rw [actual_fibre_raw_is_filter]
  exact (raw_slots_nodup v e t).filter _

#print axioms orderedSlots_perm
#print axioms actual_fibre_raw_is_filter
#print axioms actual_cycle_nodup
end F5R61

