import Std.Tactic

namespace F5R61
set_option autoImplicit false

def nextIndex (size a b : Nat) : Prop := b = a+1 ∨ (a+1 = size ∧ b = 0)

def separated (size a b : Nat) : Prop := ¬nextIndex size a b ∧ ¬nextIndex size b a

theorem balanced_pairs_nonadjacent (pairs extras i : Nat) (h : 2 ≤ pairs) (hi : i < pairs) :
    separated (2*pairs+extras) i (pairs+i) := by
  unfold separated nextIndex
  omega

theorem one_pair_nonadjacent (extras : Nat) (h : 2 ≤ extras) :
    separated (2+extras) 0 2 := by
  unfold separated nextIndex
  omega

def orderedSlots {P : Type} (pairs : List (P × P)) (extra : List P) : List P :=
  match pairs, extra with
  | [p], u :: v :: rest => p.1 :: u :: p.2 :: v :: rest
  | _, _ => pairs.map Prod.fst ++ pairs.map Prod.snd ++ extra

theorem orderedSlots_size {P : Type} (pairs : List (P × P)) (extra : List P) :
    (orderedSlots pairs extra).length = 2*pairs.length + extra.length := by
  cases pairs with
  | nil => simp [orderedSlots]
  | cons p rest =>
    cases rest with
    | nil =>
      cases extra with
      | nil => simp [orderedSlots]
      | cons u us => cases us <;> simp [orderedSlots] <;> omega
    | cons q qs => simp [orderedSlots]; omega

theorem preserves_all_original_slots {P : Type} (pairs : List (P × P)) (extra : List P) (p : P) :
    p ∈ orderedSlots pairs extra ↔ p ∈ pairs.map Prod.fst ∨ p ∈ pairs.map Prod.snd ∨ p ∈ extra := by
  cases pairs with
  | nil => simp [orderedSlots]
  | cons q qs =>
    cases qs with
    | nil =>
      cases extra with
      | nil => simp [orderedSlots]
      | cons u us =>
        cases us with
        | nil => simp [orderedSlots]
        | cons v rest =>
          simp [orderedSlots,or_left_comm,or_comm]
    | cons r rs => simp [orderedSlots,List.mem_append,or_assoc]

#print axioms balanced_pairs_nonadjacent
#print axioms one_pair_nonadjacent
#print axioms orderedSlots_size
#print axioms preserves_all_original_slots
end F5R61


