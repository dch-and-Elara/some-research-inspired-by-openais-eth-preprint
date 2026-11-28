import J7R9Clause
import J7R9EqualityTree
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Pi
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Count-preserving literal CNF-to-equality-tree compilation

Original ports are actual list indices (clause number, literal
number). Each variable gets the explicit trivalent caterpillar and
fresh internal wires. The successful original CNF assignments and
successful old network wire assignments are in bijection.
-/

open Std.Sat
open scoped BigOperators

namespace J7R9Compiler
open J7R9EqualityTree

section Positions
variable {V : Type*}

abbrev ClauseIndex (F : CNF V) := Fin F.length
abbrev Occurrence (F : CNF V) := Σ i : ClauseIndex F, Fin (F.get i).length

def literal (F : CNF V) (o : Occurrence F) : V × Bool := (F.get o.1).get o.2

theorem sat_at_positions (F : CNF V) (x : V → Bool) :
    CNF.Sat x F ↔ ∀ i : ClauseIndex F, ∃ j : Fin (F.get i).length,
      x (literal F ⟨i,j⟩).1=(literal F ⟨i,j⟩).2 := by
  unfold CNF.Sat CNF.eval
  rw [List.all_eq_true]
  constructor
  · intro h i
    obtain ⟨l,hl,he⟩ := (J7R9Clause.eval_true x (F.get i)).mp (h _ (List.get_mem _ _))
    obtain ⟨j,hj⟩ := List.get_of_mem hl
    exact ⟨j,by rw [show literal F ⟨i,j⟩=l from hj]; exact he⟩
  · intro h c hc
    obtain ⟨i,rfl⟩ := List.get_of_mem hc
    obtain ⟨j,hj⟩ := h i
    exact (J7R9Clause.eval_true x _).mpr ⟨_,List.get_mem _ j,hj⟩

theorem variable_position_iff (F : CNF V) (v : V) :
    CNF.Mem v F ↔ ∃ o : Occurrence F, (literal F o).1=v := by
  constructor
  · rintro ⟨c,hc,hm⟩
    obtain ⟨i,rfl⟩ := List.get_of_mem hc
    rcases hm with hm|hm
    · obtain ⟨j,hj⟩ := List.get_of_mem hm
      exact ⟨⟨i,j⟩,congrArg Prod.fst hj⟩
    · obtain ⟨j,hj⟩ := List.get_of_mem hm
      exact ⟨⟨i,j⟩,congrArg Prod.fst hj⟩
  · rintro ⟨⟨i,j⟩,hj⟩
    apply CNF.mem_of (List.get_mem F i)
    have hh := CNF.Clause.mem_of (List.get_mem (F.get i) j)
    simpa [literal] using (show CNF.Clause.Mem v (F.get i) from hj ▸ hh)

end Positions

variable {V : Type*} [DecidableEq V]

/-- Deterministic finite graph record up to the ordering chosen for
the finite occurrence list. All labels remain original literal indices. -/
noncomputable def occurrences (F : CNF V) (v : V) : List (Occurrence F) :=
  ((Finset.univ : Finset (Occurrence F)).filter (fun o => (literal F o).1=v)).toList

theorem mem_occurrences (F : CNF V) (v : V) (o : Occurrence F) :
    o ∈ occurrences F v ↔ (literal F o).1=v := by
  simp [occurrences]

abbrev Internal (F : CNF V) := Σ v : V, Fin ((occurrences F v).length-3)
abbrev Wire (F : CNF V) := Occurrence F ⊕ Internal F

def owner (F : CNF V) : Wire F → V
  | .inl o => (literal F o).1
  | .inr k => k.1

noncomputable def external (F : CNF V) (v : V) : List (Wire F) :=
  (occurrences F v).map Sum.inl

noncomputable def internal (F : CNF V) (v : V) : List (Wire F) :=
  List.ofFn (fun j : Fin ((occurrences F v).length-3) => Sum.inr (⟨v,j⟩ : Internal F))

noncomputable def variableGates (F : CNF V) (v : V) : List (List (Wire F)) :=
  gates (external F v) (internal F v)

theorem treeShape (F : CNF V) (v : V) :
    shape (external F v).length (internal F v).length := by
  simp [shape,external,internal]

theorem external_member (F : CNF V) (v : V) (o : Occurrence F) :
    (Sum.inl o : Wire F) ∈ external F v ↔ (literal F o).1=v := by
  simp [external,mem_occurrences]

theorem internal_member (F : CNF V) (v : V) (j : Internal F) :
    (Sum.inr j : Wire F) ∈ internal F v ↔ j.1=v := by
  constructor
  · intro h
    obtain ⟨k,hk⟩ := List.mem_ofFn.mp h
    exact (congrArg Sigma.fst (Sum.inr.inj hk)).symm
  · intro h
    rcases j with ⟨w,k⟩
    dsimp only at h
    subst w
    exact List.mem_ofFn.mpr ⟨k,rfl⟩

/-- Every external/internal wire is in exactly its own variable tree,
and all actual ports of that variable are included. -/
theorem member_owns (F : CNF V) (v : V) (w : Wire F) :
    w ∈ external F v++internal F v ↔ owner F w=v := by
  cases w with
  | inl o => simp [owner,internal,List.mem_ofFn,external_member]
  | inr k => simp [owner,external,List.mem_map,internal_member]

def clausesOK (F : CNF V) (x : Wire F → Bool) : Prop :=
  ∀ i : ClauseIndex F, ∃ j : Fin (F.get i).length, x (.inl ⟨i,j⟩)=(literal F ⟨i,j⟩).2

def varsOK (F : CNF V) (x : Wire F → Bool) : Prop :=
  ∀ v g, g ∈ variableGates F v → agrees x g

def oldOK (F : CNF V) (x : Wire F → Bool) : Prop :=
  clausesOK F x ∧ varsOK F x

def encode (F : CNF V) (x : V → Bool) : Wire F → Bool := fun w => x (owner F w)

theorem encode_ok (F : CNF V) (x : V → Bool) :
    oldOK F (encode F x) ↔ CNF.Sat x F := by
  unfold oldOK
  have hcl : clausesOK F (encode F x) ↔ CNF.Sat x F := (sat_at_positions F x).symm
  rw [hcl]
  refine ⟨And.left,fun h => ⟨h,?_⟩⟩
  intro v
  apply (gates_agree _ _ _ (treeShape F v)).mpr
  refine ⟨x v,?_⟩
  intro w hw
  unfold encode
  rw [(member_owns F v w).mp hw]

abbrev AllOccur (F : CNF V) := ∀ v : V, ∃ o : Occurrence F, (literal F o).1=v

noncomputable def anchor (F : CNF V) (h : AllOccur F) (v : V) : Wire F :=
  .inl (Classical.choose (h v))

theorem anchor_owner (F : CNF V) (h : AllOccur F) (v : V) :
    owner F (anchor F h v)=v :=
  Classical.choose_spec (h v)

noncomputable def decode (F : CNF V) (h : AllOccur F) (x : Wire F → Bool) : V → Bool :=
  fun v => x (anchor F h v)

theorem decode_encode (F : CNF V) (h : AllOccur F) (x : V → Bool) :
    decode F h (encode F x)=x := by
  funext v
  exact congrArg x (anchor_owner F h v)

theorem encode_decode (F : CNF V) (h : AllOccur F) (x : Wire F → Bool) (hx : varsOK F x) :
    encode F (decode F h x)=x := by
  funext w
  let v := owner F w
  obtain ⟨b,hb⟩ := (gates_agree x _ _ (treeShape F v)).mp (hx v)
  have hw : w ∈ external F v++internal F v := (member_owns F v w).mpr rfl
  have ha : anchor F h v ∈ external F v++internal F v :=
    (member_owns F v (anchor F h v)).mpr (anchor_owner F h v)
  exact (hb _ ha).trans (hb _ hw).symm

noncomputable def oldModelsEquiv (F : CNF V) (h : AllOccur F) :
    {x : V → Bool // CNF.Sat x F} ≃ {u : Wire F → Bool // oldOK F u} where
  toFun x := ⟨encode F x.val,(encode_ok F x.val).mpr x.property⟩
  invFun u := ⟨decode F h u.val,(encode_ok F _).mp (by
    rw [encode_decode F h _ u.property.2]
    exact u.property)⟩
  left_inv x := Subtype.ext (decode_encode F h x.val)
  right_inv u := Subtype.ext (encode_decode F h u.val u.property.2)

variable [Fintype V]

omit [DecidableEq V] in
theorem modelCount_card (F : CNF V) :
    PinnedCNF.modelCount F=Nat.card {x : V → Bool // CNF.Sat x F} := by
  classical
  rw [← Fintype.card_eq_nat_card]
  unfold PinnedCNF.modelCount
  symm
  apply Fintype.subtype_card
  intro x
  simp [CNF.Sat]

theorem literal_old_count (F : CNF V) (h : AllOccur F) :
    Nat.card {x : Wire F → Bool // oldOK F x}=PinnedCNF.modelCount F := by
  rw [modelCount_card]
  exact Nat.card_congr (oldModelsEquiv F h).symm

#print axioms sat_at_positions
#print axioms variable_position_iff
#print axioms member_owns
#print axioms encode_ok
#print axioms oldModelsEquiv
#print axioms literal_old_count

end J7R9Compiler

