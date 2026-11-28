import J7R9Compiler
import J7R9DirectedTree

/-!
# Literal source subdivision and guarded count preservation

The old clause and equality-tree nodes have explicit half-edge
addresses. Each original wire contributes a new binary equality on
its two half edges. Collapsing a successful pair is a bijection, not
merely an arithmetical equality of two sums.
-/

open Std.Sat
open scoped BigOperators

namespace J7R9Subdivision
open J7R9Compiler J7R9EqualityTree J7R9DirectedTree
variable {V : Type*} [DecidableEq V]

abbrev Half (F : CNF V) := Wire F × Bool

/-- The true external half joins the variable tree to its subdivision.
The false external half belongs to the old clause. -/
noncomputable def physicalVar (F : CNF V) (v : V) : List (List (Half F)) :=
  halfGates ((external F v).map (fun w => (w,true))) (internal F v)

theorem physical_var_degree (F : CNF V) (v : V) :
    ∀ g ∈ physicalVar F v, g.length≤3 := by
  unfold physicalVar
  apply half_degree
  simpa only [List.length_map] using treeShape F v

def physicalClause (F : CNF V) (x : Half F → Bool) : Prop :=
  ∀ i : ClauseIndex F, ∃ j : Fin (F.get i).length,
    x (.inl ⟨i,j⟩,false)=(literal F ⟨i,j⟩).2

def physicalOldOK (F : CNF V) (x : Half F → Bool) : Prop :=
  physicalClause F x ∧ ∀ v g, g ∈ physicalVar F v → agrees x g

/-- One actual new binary equality for each original wire. -/
def newOK (F : CNF V) (x : Half F → Bool) : Prop :=
  ∀ w : Wire F, x (w,false)=x (w,true)

def bipolarOK (F : CNF V) (x : Half F → Bool) : Prop :=
  physicalOldOK F x ∧ newOK F x

def lift (F : CNF V) (x : Wire F → Bool) : Half F → Bool := fun w => x w.1
def collapse (F : CNF V) (x : Half F → Bool) : Wire F → Bool := fun w => x (w,false)

theorem lift_collapse (F : CNF V) (x : Half F → Bool) (h : newOK F x) :
    lift F (collapse F x)=x := by
  funext z
  rcases z with ⟨w,b⟩
  cases b
  · rfl
  · exact h w

theorem old_under_lift (F : CNF V) (x : Wire F → Bool) :
    physicalOldOK F (lift F x) ↔ oldOK F x := by
  unfold physicalOldOK oldOK
  apply Iff.and Iff.rfl
  unfold varsOK
  apply forall_congr'
  intro v
  have h := same_bit_eval x ((external F v).map (fun w => (w,true))) (internal F v)
  have hm : (((external F v).map (fun w => (w,true))).map Prod.fst)=external F v := by
    induction external F v with
    | nil => rfl
    | cons a t ih => simp [ih]
  rw [hm] at h
  exact h

theorem network_under_lift (F : CNF V) (x : Wire F → Bool) :
    bipolarOK F (lift F x) ↔ oldOK F x := by
  unfold bipolarOK
  rw [old_under_lift]
  exact ⟨And.left,fun h => ⟨h,fun _ => rfl⟩⟩

noncomputable def subdivisionEquiv (F : CNF V) :
    {x : Wire F → Bool // oldOK F x} ≃ {x : Half F → Bool // bipolarOK F x} where
  toFun x := ⟨lift F x.val,(network_under_lift F x.val).mpr x.property⟩
  invFun x := ⟨collapse F x.val,(network_under_lift F _).mp (by
    rw [lift_collapse F x.val x.property.2]
    exact x.property)⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext (lift_collapse F x.val x.property.2)

variable [Fintype V]

theorem subdivision_count (F : CNF V) (h : AllOccur F) :
    Nat.card {x : Half F → Bool // bipolarOK F x}=PinnedCNF.modelCount F := by
  rw [← literal_old_count F h]
  exact Nat.card_congr (subdivisionEquiv F).symm

omit [DecidableEq V] in
/-- If the declared variable type is nonempty, every guarded variable,
including the fresh guard, occurs in the literal guard constraints.
The zero-variable exceptional case need not use a tensor entry call. -/
theorem guard_allOccur [Nonempty V] (F : CNF V) :
    AllOccur (J6Guard.guardedFormula F) := by
  intro a
  apply (variable_position_iff _ a).mp
  have incl (v : V) : ([(none,true),(some v,false)] : CNF.Clause (Option V)) ∈
      J6Guard.guardedFormula F := by
    unfold J6Guard.guardedFormula
    apply List.mem_append.mpr
    right
    apply List.mem_map.mpr
    exact ⟨v,by simp,rfl⟩
  cases a with
  | none =>
    obtain ⟨v⟩ := (inferInstance : Nonempty V)
    exact CNF.mem_of (incl v) (CNF.Clause.mem_of (p:=true) (by simp))
  | some v =>
    exact CNF.mem_of (incl v) (CNF.Clause.mem_of (p:=false) (by simp))

theorem guarded_subdivision_count [Nonempty V] (F : CNF V) :
    let H := J6Guard.guardedFormula (J7R9Clause.clean F)
    Nat.card {x : Half H → Bool // bipolarOK H x}=1+PinnedCNF.modelCount F := by
  dsimp only
  rw [subdivision_count _ (guard_allOccur _),J7R9Clause.guarded_clean_count]

#print axioms physical_var_degree
#print axioms subdivisionEquiv
#print axioms subdivision_count
#print axioms guard_allOccur
#print axioms guarded_subdivision_count

end J7R9Subdivision

