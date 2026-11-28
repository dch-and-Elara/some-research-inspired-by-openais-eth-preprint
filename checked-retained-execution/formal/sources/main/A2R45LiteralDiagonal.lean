
import A2R45LiteralInput
import Mathlib.Data.Fin.SuccPred

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5000000
set_option maxRecDepth 1850
set_option linter.unusedSectionVars false

/-! The publicly padded diagonal in the frozen fixed-graph encoding is
a source-topology difference, not a new counted choice in the shifted
logical contraction. Erase that occurrence from each vertex path, and
splice the surviving consecutive equalities. Restriction of genuine
assignments to precisely the distinct-pair endpoints is an equivalence. -/
namespace A2R45Literal
open scoped Classical BigOperators
open FixedHostAcquisition
noncomputable section

abbrev DistinctOccurrence (n : ℕ) :=
  {o : Occurrence n // o.1≠o.2}

variable {k : ℕ}
local notation "n" => k+1
local notation "V" => Vertex (k+1)
local notation "D" => DistinctOccurrence (k+1)

def trimIndex (v : V) (i : Fin (k+1)) : D :=
  ⟨(v,v.succAbove i),v.ne_succAbove i⟩

theorem all_nondiagonal (o : D) : ∃ i : Fin (k+1), trimIndex o.val.1 i=o := by
  obtain ⟨i,hi⟩ := Fin.exists_succAbove_eq o.property.symm
  refine ⟨i,Subtype.ext ?_⟩
  exact Prod.ext rfl hi

def trimmedOrder : V×Fin (k+1)≃D :=
  Equiv.ofBijective (fun q : V×Fin (k+1)=>trimIndex q.1 q.2) (by
    constructor
    · intro x y h
      have p : x.1=y.1 := congrArg (fun t : D=>t.val.1) h
      have q := congrArg (fun t : D=>t.val.2) h
      apply Prod.ext p
      change x.1.succAbove x.2=y.1.succAbove y.2 at q
      rw [←p] at q
      exact Fin.succAbove_right_injective q
    · intro o
      obtain ⟨i,h⟩ := all_nondiagonal o
      exact ⟨(o.val.1,i),h⟩)

def trimPair (e : Pair n) : Bool→D
  | false=>⟨pairOccurrence e false,e.property.ne⟩
  | true=>⟨pairOccurrence e true,e.property.ne.symm⟩

def eraseDiagonal (X : Occurrence n→Bool) : D→Bool :=
  fun o=>X o.val

def restoreDiagonal (X : D→Bool) : Occurrence n→Bool :=
  liftVertices (fun v=>X (trimIndex v 0))

def trimCoherent (X : D→Bool) : Prop :=
  ∀ (v : V) (i : Fin k), X (trimIndex v i.castSucc)=X (trimIndex v i.succ)

def trimmedPairAccepted (e : Pair n) (enabled : Pair n→Bool) (X : D→Bool) : Prop :=
  enabled e=true → ¬(X (trimPair e false)=true ∧ X (trimPair e true)=true)

theorem trimmed_path_constant (X : D→Bool) (hX : trimCoherent X)
    (v : V) (j : Fin (k+1)) : X (trimIndex v 0)=X (trimIndex v j) := by
  induction j using Fin.induction with
  | zero => rfl
  | succ i ih => exact ih.trans (hX v i)

theorem restrict_keeps_same_pair_gate (enabled : Pair n→Bool)
    (X : Occurrence n→Bool) (e : Pair n) :
    trimmedPairAccepted e enabled (eraseDiagonal X) ↔ PairAccepted enabled X e := Iff.rfl

theorem trim_coherent_of_full (X : Occurrence n→Bool) (hX : coherent X) :
    trimCoherent (eraseDiagonal X) := by
  obtain ⟨x,rfl⟩ := (coherent_iff X).mp hX
  intro v i
  rfl

theorem restore_is_coherent (X : D→Bool) : coherent (restoreDiagonal X) :=
  (coherent_iff _).mpr ⟨_,rfl⟩

theorem restored_is_extension (X : D→Bool) (hX : trimCoherent X) :
    eraseDiagonal (restoreDiagonal X)=X := by
  funext o
  obtain ⟨j,hj⟩ := all_nondiagonal o
  change X (trimIndex o.val.1 0)=X o
  exact (trimmed_path_constant X hX o.val.1 j).trans (congrArg X hj)

theorem restore_after_erase_eq (X : Occurrence n→Bool) (hX : coherent X) :
    restoreDiagonal (eraseDiagonal X)=X := by
  obtain ⟨x,rfl⟩ := (coherent_iff X).mp hX
  rfl

abbrev PaddedAccepted (enabled : Pair n→Bool) :=
  {X : Occurrence n→Bool // coherent X ∧ ∀ e,PairAccepted enabled X e}

abbrev TrimmedAccepted (enabled : Pair n→Bool) :=
  {X : D→Bool // trimCoherent X ∧ ∀ e,trimmedPairAccepted e enabled X}

def erase_diagonal_equiv (enabled : Pair n→Bool) :
    PaddedAccepted enabled≃TrimmedAccepted enabled where
  toFun X := ⟨eraseDiagonal X.val,trim_coherent_of_full X.val X.property.1,
    fun e=>(restrict_keeps_same_pair_gate enabled X.val e).mpr (X.property.2 e)⟩
  invFun X := ⟨restoreDiagonal X.val,restore_is_coherent X.val,by
    intro e
    apply (restrict_keeps_same_pair_gate enabled _ e).mp
    rw [restored_is_extension X.val X.property.1]
    exact X.property.2 e⟩
  left_inv X := Subtype.ext (restore_after_erase_eq X.val X.property.1)
  right_inv X := Subtype.ext (restored_is_extension X.val X.property.1)

theorem same_number_of_shifted_accepting_assignments (enabled : Pair n→Bool) :
    Nat.card (PaddedAccepted enabled)=Nat.card (TrimmedAccepted enabled) :=
  Nat.card_congr (erase_diagonal_equiv enabled)

private def accepted_vertex_equiv (enabled : Pair n→Bool) :
    {x : V→Bool // IsIndependent enabled x}≃PaddedAccepted enabled where
  toFun x := ⟨liftVertices x.val,(coherent_iff _).mpr ⟨x.val,rfl⟩,x.property⟩
  invFun X := ⟨fun v=>X.val (v,0),by
    obtain ⟨x,hx⟩ := (coherent_iff X.val).mp X.property.1
    have h : (fun v=>X.val (v,0))=x := funext (fun v=>(congrFun hx (v,0)).symm)
    rw [h]
    have prop := X.property.2
    rw [←hx] at prop
    exact prop⟩
  left_inv _ := rfl
  right_inv X := by
    apply Subtype.ext
    obtain ⟨x,hx⟩ := (coherent_iff X.val).mp X.property.1
    change liftVertices (fun v=>X.val (v,0))=X.val
    rw [←hx]
    rfl

theorem trimmed_exact_graph_count (enabled : Pair n→Bool) :
    Nat.card (TrimmedAccepted enabled)=count enabled := by
  rw [←same_number_of_shifted_accepting_assignments,
    ←Nat.card_congr (accepted_vertex_equiv enabled),Nat.card_eq_fintype_card]
  unfold count
  exact Fintype.card_subtype (IsIndependent enabled)

theorem trimmed_occurrence_card :
    Nat.card D=(k+2)*(k+1) := by
  rw [←Nat.card_congr (trimmedOrder (k:=k)),Nat.card_prod,Nat.card_fin,Nat.card_fin]

theorem trimmed_free_columns :
    Nat.card (D→Bool)=2^((k+2)*(k+1)) := by
  rw [Nat.card_fun,trimmed_occurrence_card (k:=k),Nat.card_eq_fintype_card (α:=Bool),Fintype.card_bool]

theorem public_origin_diagonal_factor :
    (2:ℕ)^((k+2)^2)=2^(k+2)*Nat.card (D→Bool) := by
  rw [trimmed_free_columns (k:=k),←pow_add]
  congr 1
  ring

#print axioms all_nondiagonal
#print axioms trimmed_path_constant
#print axioms restrict_keeps_same_pair_gate
#print axioms erase_diagonal_equiv
#print axioms same_number_of_shifted_accepting_assignments
#print axioms trimmed_exact_graph_count
#print axioms trimmed_occurrence_card
#print axioms public_origin_diagonal_factor
end
end A2R45Literal
