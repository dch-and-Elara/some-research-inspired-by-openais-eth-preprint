import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4500000

/-! This is the exact ordering primitive used by R26 modeOrdinal.
Merely validating a complete duplicate-free alphabet leaves its
ordinal unspecified. The raw event may therefore remain the same
while two legal legacy ordering receipts demand different bits. -/
namespace J6R50ModeDispatch

def legacyIndex {X : Type*} [DecidableEq X] (xs : List X) (nd : xs.Nodup)
    (all : ∀ x,x∈xs) (x : X) :=
  ((List.Nodup.getEquivOfForallMemList xs nd all).symm x).val

theorem literal_swap_changes_legacy_index {X : Type*} [DecidableEq X]
    (x y : X) (xs : List X)
    (nd : (x::y::xs).Nodup) (all : ∀ b,b∈x::y::xs)
    (nd' : (y::x::xs).Nodup) (all' : ∀ b,b∈y::x::xs) :
    legacyIndex (x::y::xs) nd all x=0 ∧ legacyIndex (y::x::xs) nd' all' x=1 := by
  have ne : x≠y := by
    intro e
    subst y
    exact (List.nodup_cons.mp nd).1 List.mem_cons_self
  constructor
  · change List.idxOf x (x::y::xs)=0
    simp
  · change List.idxOf x (y::x::xs)=1
    simp [ne.symm]

theorem no_layout_free_ordinal_on_same_event {X B : Type*} [DecidableEq X]
    (x y : X) (xs : List X) (nd : (x::y::xs).Nodup) (all : ∀ b,b∈x::y::xs)
    (raw : B) (decode : B  →  ℕ) :
    ∃ (nd' : (y::x::xs).Nodup) (all' : ∀ b,b∈y::x::xs),
      ¬ (decode raw=legacyIndex (x::y::xs) nd all x ∧
        decode raw=legacyIndex (y::x::xs) nd' all' x) := by
  have swap : (x::y::xs).Perm (y::x::xs) := List.Perm.swap y x xs
  let nd' := swap.nodup_iff.mp nd
  let all' (b : X) := swap.mem_iff.mp (all b)
  obtain ⟨h,k⟩ := literal_swap_changes_legacy_index x y xs nd all nd' all'
  refine ⟨nd',all',?_⟩
  intro bad
  rw [h,k] at bad
  omega

#print axioms literal_swap_changes_legacy_index
#print axioms no_layout_free_ordinal_on_same_event
end J6R50ModeDispatch

