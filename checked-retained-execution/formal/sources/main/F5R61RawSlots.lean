import F5R61GeneratedCycles
import F5R60SourceSizes
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Dedup

namespace F5R61
open F5R60
set_option autoImplicit false
set_option linter.unusedSimpArgs false

theorem nodup_if_finset_full_length {A : Type} [DecidableEq A] {L : List A}
    (eq : L.toFinset.card = L.length) : L.Nodup := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    rw [List.toFinset_cons] at eq
    by_cases m : x ∈ xs.toFinset
    · rw [Finset.insert_eq_of_mem m] at eq
      have le := List.toFinset_card_le xs
      simp only [List.length_cons] at eq
      omega
    · rw [Finset.card_insert_of_notMem m,List.length_cons] at eq
      exact List.Nodup.cons (fun h => m (List.mem_toFinset.mpr h)) (ih (Nat.add_right_cancel eq))

theorem listing_has_exact_size {A : Type} [Fintype A] (l : Listing A) :
    l.elems.length = Fintype.card A := by
  classical
  have h : l.elems.toFinset = Finset.univ := by
    ext a
    simp [l.all a]
  rw [← List.toFinset_card_of_nodup l.once,h,Fintype.card]

theorem flatMap_width {A P : Type} (f : A → List P) (w : Nat)
    (each : ∀ a, (f a).length=w) (Q : List A) :
    (Q.flatMap f).length=Q.length*w := by
  induction Q with
  | nil => simp
  | cons a rest ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, each, ih, Nat.add_mul, Nat.one_mul]
    omega

variable {V E T : Type}

def rawSourceSlots (v : Listing V) (e : Listing E) (t : Listing T) : List (PrivatePos V E T) :=
  ((allForbidden v e t).map Prod.fst ++ (allForbidden v e t).map Prod.snd) ++ allSingles e t

theorem raw_slots_length (v : Listing V) (e : Listing E) (t : Listing T) :
    (rawSourceSlots v e t).length = 2*v.elems.length+5*e.elems.length+10*t.elems.length := by
  unfold rawSourceSlots
  have Ecount := flatMap_width (edgeSingles (V:=V) (T:=T)) 3 (fun _ => rfl) e.elems
  have Tcount := flatMap_width (tripleSingles (V:=V) (E:=E)) 8 (fun _ => rfl) t.elems
  simp only [List.length_append,List.length_map,allForbidden,switches,directedRequests,tripleRequests,
    allSingles,Ecount,Tcount]
  omega

theorem raw_slots_nodup [Fintype V] [Fintype E] [Fintype T]
    (v : Listing V) (e : Listing E) (t : Listing T) : (rawSourceSlots v e t).Nodup := by
  classical
  letI : Fintype (PrivatePos V E T) := privatePositionsFintype
  have h : (rawSourceSlots v e t).toFinset = Finset.univ := by
    ext p
    simp only [List.mem_toFinset,Finset.mem_univ,iff_true]
    rcases every_source_slot_listed v e t p with h|h|h
    · exact List.mem_append_left _ (List.mem_append_left _ h)
    · exact List.mem_append_left _ (List.mem_append_right _ h)
    · exact List.mem_append_right _ h
  apply nodup_if_finset_full_length
  rw [h,Finset.card_univ,actual_private_slots,raw_slots_length,
    listing_has_exact_size v,listing_has_exact_size e,listing_has_exact_size t]
  rfl

#print axioms nodup_if_finset_full_length
#print axioms listing_has_exact_size
#print axioms flatMap_width
#print axioms raw_slots_length
#print axioms raw_slots_nodup
end F5R61
