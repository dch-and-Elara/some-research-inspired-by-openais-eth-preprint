import J6R49CostRecurrence

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 14000000
set_option maxRecDepth 2700

/-! Lift the actual occurrence tree to ancestor-indexed scope states,
without merging equal child records or imposing cache deduplication. -/
namespace J6R49Cost
open scoped BigOperators
open J6R10Reachable J6R16ModeCost J6R24MeteredRecursion

universe u v w
variable {X : Type u}

def scopePlan (P : FinitePlan.{u,v} X) (Y : X → Type w)
    (next : ∀ z : Sigma Y, ∀ k : P.Slot z.1, Y (P.child z.1 k)) :
    FinitePlan (Sigma Y) where
  size z := P.size z.1
  Slot z := P.Slot z.1
  finiteSlot z := P.finiteSlot z.1
  child z k := ⟨P.child z.1 k,next z k⟩
  smaller z k := P.smaller z.1 k

theorem scope_children_project (P : FinitePlan.{u,v} X) (Y : X → Type w)
    (next : ∀ z : Sigma Y, ∀ k : P.Slot z.1, Y (P.child z.1 k))
    (z : Sigma Y) :
    (childList (scopePlan P Y next) z).map Sigma.fst=childList P z.1 := by
  rw [childList,List.map_map]
  rfl

theorem scope_occurrences_project (P : FinitePlan.{u,v} X) (Y : X → Type w)
    (next : ∀ z : Sigma Y, ∀ k : P.Slot z.1, Y (P.child z.1 k))
    (r : Sigma Y) (d : ℕ) :
    (occurrences (scopePlan P Y next) r d).map Sigma.fst=occurrences P r.1 d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [occurrences,occurrences,List.map_flatMap,←ih,List.flatMap_map]
    apply List.flatMap_congr
    intro z _
    exact scope_children_project P Y next z

theorem scoped_occurrence_upper (P : FinitePlan.{u,v} X) (Y : X → Type w)
    (next : ∀ z : Sigma Y, ∀ k : P.Slot z.1, Y (P.child z.1 k)) (r : Sigma Y)
    (s C lam K b H fixed address : ℕ) (total localFee : Sigma Y → ℕ)
    (terminal : occurrences P r.1 (H+1)=[])
    (hSlots : ∀ j x,x∈occurrences P r.1 j →
      Nat.card (P.Slot x) ≤ 2^(b+depthExponent s C lam K j))
    (runStep : ∀ j z,z∈occurrences (scopePlan P Y next) r j →
      total z ≤ localFee z+((childList (scopePlan P Y next) z).map total).sum)
    (ownBound : ∀ j z,z∈occurrences (scopePlan P Y next) r j →
      localFee z ≤ fixed+address*Nat.card (P.Slot z.1)) :
    total r ≤ (H+1)*(fixed+address)*2^(b*(H+1)+24*depthScale s C lam K) := by
  let Q := scopePlan P Y next
  have hTerm : occurrences Q r (H+1)=[] := by
    have p := scope_occurrences_project P Y next r (H+1)
    rw [terminal] at p
    exact List.map_eq_nil_iff.mp p
  have hFan (j : ℕ) (z : Sigma Y) (hz : z∈occurrences Q r j) :
      Nat.card (Q.Slot z) ≤ 2^(b+depthExponent s C lam K j) := by
    have m : z.1∈(occurrences Q r j).map Sigma.fst := List.mem_map_of_mem (f:=Sigma.fst) hz
    rw [scope_occurrences_project P Y next] at m
    exact hSlots j z.1 m
  exact affine_occurrence_tree_bound Q r s C lam K b H fixed address total localFee hTerm hFan runStep ownBound

#print axioms scopePlan
#print axioms scope_children_project
#print axioms scope_occurrences_project
#print axioms scoped_occurrence_upper
end J6R49Cost

