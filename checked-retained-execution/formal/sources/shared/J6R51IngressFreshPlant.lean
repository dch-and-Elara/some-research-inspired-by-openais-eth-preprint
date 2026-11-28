import J6R51IngressOccurrence
import J7R10Plant

/-! A fresh legal Plant whose wire ordinals are genuine list ranks
computed from input encounter order and the declared variable roster.
The new graph uses the same literal gates and caterpillar recipe. -/
namespace J6R51Ingress
noncomputable section
open scoped Classical BigOperators
open Std.Sat J7R9Compiler J7R9Subdivision J7R10Ports J7R10Counts J7R10Plant
open J7R9EqualityTree J6OrientedHost J6OrientedHostEval J6RecursivePortCube
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 16800000
set_option maxRecDepth 2600

variable {V : Type*} [DecidableEq V] (H : CNF V)
abbrev OrderedTree := Σ v : V, Fin (orderedVar H v).length
abbrev OrderedOld := ClauseIndex H ⊕ OrderedTree H

def orderedDegree : OrderedOld H→ℕ
  | .inl i => (H.get i).length
  | .inr ⟨v,j⟩ => ((orderedVar H v).get j).length

abbrev OrderedPort := Σ v : OrderedOld H, Fin (orderedDegree H v)

def orderedPort : (v : OrderedOld H)→Fin (orderedDegree H v)→Half H
  | .inl i,j => (.inl ⟨i,j⟩,false)
  | .inr ⟨v,k⟩,j => ((orderedVar H v).get k).get j

def rowHalf (p : OrderedPort H) : Half H := orderedPort H p.1 p.2

def orderedGate : (v : OrderedOld H)→Gate (orderedDegree H v)
  | .inl i => .clause (fun j => (literal H ⟨i,j⟩).2)
  | .inr _ => .equal

theorem ordered_width (D : ℕ) (h : ∀ row∈H,row.length≤D) (v : OrderedOld H) :
    orderedDegree H v≤max D 3 := by
  rcases v with i|⟨v,k⟩
  · exact (h _ (List.get_mem _ i)).trans (le_max_left _ _)
  · exact (ordered_degree H v (List.get_mem _ k)).trans (le_max_right _ _)

variable [Fintype V]

theorem ordered_port_count (w : Half H) :
    (∑ p : OrderedPort H, if rowHalf H p=w then (1:ℕ) else 0)=1 := by
  apply Eq.trans _ (counts_cover H w)
  rw [Fintype.sum_sigma,Fintype.sum_sum_type]
  congr 1
  · unfold clauseCount
    rw [Fintype.sum_sigma]
    rfl
  · unfold variableCount
    rw [Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro v _
    calc
      (∑ j : Fin (orderedVar H v).length, ∑ k : Fin (((orderedVar H v).get j).length),
           if ((orderedVar H v).get j).get k=w then (1:ℕ) else 0) =
          ∑ j : Fin (orderedVar H v).length, countByEq (List.get (orderedVar H v) j) w := by
            apply Finset.sum_congr rfl
            intro i _
            exact (count_positions ((orderedVar H v).get i) w).symm
      _ = countByEq (orderedVar H v).flatten w := (flatten_positions _ _).symm
      _ = _ := ordered_var_flat_count H v w
theorem ordered_unique_port (w : Half H) :
    ∃! p : OrderedPort H,rowHalf H p=w := by
  let s := (Finset.univ : Finset (OrderedPort H)).filter (fun p => rowHalf H p=w)
  have K : s.card=1 := by unfold s; rw [Finset.card_filter,ordered_port_count]
  obtain ⟨p,hp⟩ := Finset.card_eq_one.mp K
  have hs (q : OrderedPort H) : rowHalf H q=w ↔ q=p := by
    have e := congrArg (fun t : Finset (OrderedPort H)=>q∈t) hp
    simpa [s] using e
  exact ⟨p,(hs p).mpr rfl,fun q hq => (hs q).mp hq⟩

noncomputable def orderedRowChart : OrderedPort H≃Half H :=
  Equiv.ofBijective (rowHalf H) ⟨by
    intro p q h
    obtain ⟨z,_,hz⟩ := ordered_unique_port H (rowHalf H p)
    exact (hz p rfl).trans (hz q h.symm).symm,by
    intro w
    obtain ⟨p,hp,_⟩ := ordered_unique_port H w
    exact ⟨p,hp⟩⟩

structure DeclaredOrder (A : Type*) where
  roster : List A
  distinct : roster.Nodup
  complete : ∀ x,x∈roster

def wireOrder (s : DeclaredOrder V) : List (Wire H) :=
  (occurrenceOrder H).map Sum.inl ++ s.roster.flatMap (internal H)

theorem wire_order_all (s : DeclaredOrder V) (w : Wire H) :
    w∈wireOrder H s := by
  rcases w with o|q
  · exact List.mem_append_left _ (List.mem_map_of_mem (occurrence_order_all H o))
  · exact List.mem_append_right _ (List.mem_flatMap.mpr
      ⟨q.1,s.complete _,(internal_member H q.1 q).mpr rfl⟩)

theorem wire_order_distinct (s : DeclaredOrder V) : (wireOrder H s).Nodup := by
  unfold wireOrder
  rw [List.nodup_append']
  refine ⟨(occurrence_order_nodup H).map Sum.inl_injective,?_,?_⟩
  · apply List.nodup_flatMap.mpr
    constructor
    · intro v _
      exact internal_nodup H v
    · apply s.distinct.imp
      intro v u h a ha hb
      rcases a with o|i
      · obtain ⟨k,K⟩ := List.mem_ofFn.mp ha
        cases K
      · exact h (((internal_member H v i).mp ha).symm.trans ((internal_member H u i).mp hb))
  · intro v ha hb
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨i,_,h⟩ := List.mem_flatMap.mp hb
    obtain ⟨k,K⟩ := List.mem_ofFn.mp h
    cases K

def halfOrder (s : DeclaredOrder V) : List (Half H) :=
  (wireOrder H s).product [false,true]

theorem half_order_all (s : DeclaredOrder V) (x : Half H) :
    x∈halfOrder H s := by
  rcases x with ⟨w,b⟩
  cases b <;> simp [halfOrder,List.mem_product,wire_order_all]

theorem half_order_distinct (s : DeclaredOrder V) :
    (halfOrder H s).Nodup :=
  List.Nodup.product (wire_order_distinct H s) (by decide)

def listRanks {A : Type*} [DecidableEq A] [Fintype A] (l : List A)
    (hd : l.Nodup) (hc : ∀ a,a∈l) : A≃Fin (Fintype.card A) :=
  (List.Nodup.getEquivOfForallMemList l hd hc).symm.trans
    (finCongr (by simpa using Fintype.card_congr (List.Nodup.getEquivOfForallMemList l hd hc)))

def indexByEq {A : Type*} [DecidableEq A] (q : A) (xs : List A) : ℕ :=
  @List.idxOf A instBEqOfDecidableEq q xs

theorem list_rank_value {A : Type*} [DecidableEq A] [Fintype A] (l : List A)
    (hd : l.Nodup) (hc : ∀ a,a∈l) (a : A) :
    (listRanks l hd hc a).val=indexByEq a l := rfl

def wireRank (s : DeclaredOrder V) : Wire H≃Fin (nSubdiv H) :=
  listRanks (wireOrder H s) (wire_order_distinct H s) (wire_order_all H s)

def halfRank (s : DeclaredOrder V) : Half H≃Fin (nWires H) :=
  listRanks (halfOrder H s) (half_order_distinct H s) (half_order_all H s)

noncomputable def freshPlant (s : DeclaredOrder V) :
    Plant (OrderedOld H) (nWires H) (nSubdiv H) where
  degree := orderedDegree H
  old := orderedGate H
  rowPort := (orderedRowChart H).trans (halfRank H s)
  colPort := (Equiv.prodCongr (wireRank H s).symm (Equiv.refl Bool)).trans (halfRank H s)

theorem live_row_rank (s : DeclaredOrder V) (p : OrderedPort H) :
    ((freshPlant H s).rowPort p).val=indexByEq (rowHalf H p) (halfOrder H s) :=
  list_rank_value (halfOrder H s) (half_order_distinct H s) (half_order_all H s) (rowHalf H p)

theorem live_col_rank (s : DeclaredOrder V) (w : Wire H) (b : Bool) :
    ((freshPlant H s).colPort (wireRank H s w,b)).val=indexByEq (w,b) (halfOrder H s) := by
  change ((halfRank H s) ((wireRank H s).symm (wireRank H s w),b)).val=_
  rw [Equiv.symm_apply_apply]
  exact list_rank_value (halfOrder H s) (half_order_distinct H s) (half_order_all H s) (w,b)
#print axioms ordered_width
#print axioms ordered_port_count
#print axioms ordered_unique_port
#print axioms wire_order_all
#print axioms wire_order_distinct
#print axioms half_order_all
#print axioms half_order_distinct
#print axioms list_rank_value
#print axioms live_row_rank
#print axioms live_col_rank
end
end J6R51Ingress
