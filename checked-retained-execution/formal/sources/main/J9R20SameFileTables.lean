
import J9R20SameFileCatalog
import J6R15SpecializedBoxOrientedSeat

/-! The earlier packed network and the R17 root have a literal port
equivalence. Also exhibit actual equality CNF syntax for all four
clone tables when a canonical input chart is desired. -/
namespace J9R20SameFile
open scoped BigOperators Classical Polynomial
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R9PacketScopes
open J6R14SpecializedBox J8EndToEnd J8Physical LiteralPortCompiler
open J7SourceLabels J7SeatSource J7ToJ8Incidence J7ToJ8Layout J7SeatPacking
noncomputable section
set_option linter.unusedSectionVars false

section PreviousReindex
variable {A Pair Row Col W : Type} [LinearOrder A] [AddCommGroup A] [Fintype A]
variable [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W] {t b : ℕ}
variable (row : W→Row) (col : W→OrdinaryColumn Pair Col)

variable (two : ∀ r, Nat.card {w : W // row w=r}=2) (state : DState A Pair Row Col t)
variable (seat : J7SourceLabels.Wire Pair W ↪ Physical (t+1) b A)
variable (same : ∀ w, physicalCell (balancedMask (t+1) b) (seat w)=wordLabel row col state w)
variable (budget : Nat.card (Page (t+1) b A)*2^(t+1) ≤ 3*Nat.card (J7SourceLabels.Wire Pair W))

theorem old_packed_and_oriented_same_chart
    (F : OldTables (physicalLayout row col two state seat same))
    (sign : Pin Pair→Bool) (f : ℤ[X]) (ell created : ℕ) (hf : f.Monic) :
    let d := physicalLayout row col two state seat same
    let E := rowWire (Pair:=Pair) row two
    let P := asOrientedSeat row col two state seat same budget
    let P' := J7R13.asPacking row col state seat same budget
    let F' := sameSeatFile row col two state seat same f ell created F sign
    let F₀ := orientedEntryFile d f ell created F sign
    (P.mask=P'.mask) ∧
    (∀ w, P.seat w=P'.seat (E w)) ∧
    (∀ v, (F' v).created=(F₀ v).created) ∧
    (∀ x v, (F' v).frozen hf (assignment (J7R13.network row col) x v) =
      (F₀ v).frozen hf (assignment (orientedNetwork d) (x∘E) v)) := by
  exact ⟨rfl,fun _ => rfl,fun _ => rfl,
    sameSeatFile_retained row col two state seat same f ell created F sign hf⟩
end PreviousReindex

section FullEqualityTables
variable {I : Type*} [Fintype I]

def fullEqualityCNF : CNF I :=
  (Finset.univ : Finset (I×I)).toList.flatMap (fun p => equality p.1 p.2)

private theorem literal_equality_true (x : I→Bool) (i j : I) :
    satisfied (equality i j) x=true ↔ x i=x j := by
  have h := truth_equality (R:=ℕ) x i j
  unfold truth indicator at h
  by_cases h₀ : x i=x j
  · simp only [if_pos h₀] at h
    cases hv : satisfied (equality i j) x <;> simp_all
  · simp only [if_neg h₀] at h
    cases hv : satisfied (equality i j) x <;> simp_all

private theorem equalityList_true (l : List (I×I)) (x : I→Bool) :
    satisfied (l.flatMap (fun p => equality p.1 p.2)) x=true ↔
      ∀ p∈l,x p.1=x p.2 := by
  induction l with
  | nil => simp [satisfied]
  | cons p xs ih =>
    have e0 : satisfied (equality p.1 p.2 ++ xs.flatMap (fun q => equality q.1 q.2)) x =
        (satisfied (equality p.1 p.2) x && satisfied (xs.flatMap (fun q => equality q.1 q.2)) x) := by
      simp only [satisfied,List.all_append]
    rw [List.flatMap_cons,e0,Bool.and_eq_true,literal_equality_true,ih]
    simp only [List.mem_cons,forall_eq_or_imp]

theorem fullEqualityCNF_true (x : I→Bool) :
    satisfied fullEqualityCNF x=true ↔ ∀ i j,x i=x j := by
  rw [fullEqualityCNF,equalityList_true]
  constructor
  · intro h i j
    exact h (i,j) (by simp)
  · intro h p _
    exact h p.1 p.2

variable {Packet R S V G : Type} {U : V→Type} {L : ℕ}
variable (d : Layout Packet R S V G U L) [(v : V) → Fintype (U v)]

def chooseAllCloneTables (F : OldTables d) (old : Finset (Option (S⊕V))) : OldTables d :=
  fun g v => if some (Sum.inr v.val)∈old then fullEqualityCNF else F g v

theorem chosenAllCloneTables_is_literal_equality (F : OldTables d) (old : Finset (Option (S⊕V))) :
    LocalCloneLaw d (chooseAllCloneTables d F old) old := by
  intro v hv x
  simp only [chooseAllCloneTables,if_pos hv,fullEqualityCNF_true]

theorem chosenAllCloneTables_preserve_other (F : OldTables d) (old : Finset (Option (S⊕V)))
    (g : G) (v : LocalColumn d g) (outside : some (Sum.inr v.val)∉old) :
    chooseAllCloneTables d F old g v=F g v := by
  simp [chooseAllCloneTables,outside]

theorem chosenAllCloneTables_satisfiable (F : OldTables d) (old : Finset (Option (S⊕V)))
    (sat : ∀ g (v : LocalColumn d g), some (Sum.inr v.val)∉old → ∃ x,satisfied (F g v) x=true) :
    ∀ g v, ∃ x,satisfied (chooseAllCloneTables d F old g v) x=true := by
  intro g v
  by_cases inside : some (Sum.inr v.val)∈old
  · refine ⟨fun _ => false,?_⟩
    rw [chooseAllCloneTables,if_pos inside,fullEqualityCNF_true]
    exact fun _ _ => rfl
  · rw [chosenAllCloneTables_preserve_other d F old g v inside]
    exact sat g v inside

end FullEqualityTables

#print axioms old_packed_and_oriented_same_chart
#print axioms fullEqualityCNF_true
#print axioms chosenAllCloneTables_is_literal_equality
#print axioms chosenAllCloneTables_preserve_other
#print axioms chosenAllCloneTables_satisfiable

end
end J9R20SameFile
