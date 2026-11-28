import J6R16ModeCostLayers

/-! Exact telescoping on the source's occurrence list. No charge is
assigned to a cache-deduplicated set of calls: if two addresses reach
the same Call record, both contribute at that level. This traversal is
a proof-side receipt; it is not a second execution of the algorithm. -/
namespace J6R24MeteredRecursion
open scoped BigOperators
open J6R10Reachable J6R16ModeCost

variable {X : Type*}

theorem list_sum_flat_map {A B : Type*} (xs : List A) (f : A→List B) (g : B→ℕ) :
    ((xs.flatMap f).map g).sum=(xs.map (fun a=>((f a).map g).sum)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons,List.map_append,List.sum_append,List.map_cons,List.sum_cons,ih]

theorem list_charge {A : Type*} (xs : List A) (a b c : A→ℕ)
    (e : ∀ x∈xs,a x=b x+c x) :
    (xs.map a).sum=(xs.map b).sum+(xs.map c).sum := by
  induction xs with
  | nil => rfl
  | cons z zs ih =>
    have head := e z List.mem_cons_self
    have tail := ih (fun w hw=>e w (List.mem_cons_of_mem _ hw))
    simp only [List.map_cons,List.sum_cons,head,tail]
    omega

noncomputable def levelBill (P : FinitePlan X) (r : X) (f : X→ℕ) (d : ℕ) : ℕ :=
  ((occurrences P r d).map f).sum

theorem next_level_bill (P : FinitePlan X) (r : X) (f : X→ℕ) (d : ℕ) :
    levelBill P r f (d+1)=
      ((occurrences P r d).map (fun x=>((childList P x).map f).sum)).sum := by
  unfold levelBill
  rw [occurrences,list_sum_flat_map]

theorem ledger_step (P : FinitePlan X) (r : X) (total localFee : X→ℕ) (d : ℕ)
    (receipt : ∀ x∈occurrences P r d,total x=localFee x+((childList P x).map total).sum) :
    levelBill P r total d=levelBill P r localFee d+levelBill P r total (d+1) := by
  rw [next_level_bill,levelBill,levelBill]
  exact list_charge _ _ _ _ receipt

theorem telescoping_ledger (a b : ℕ→ℕ) (step : ∀ d,a d=b d+a (d+1)) (n : ℕ) :
    a 0=(∑ j∈Finset.range n,b j)+a n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,step n]
    omega

theorem occurrence_tree_ledger (P : FinitePlan X) (r : X) (total localFee : X→ℕ) (H : ℕ)
    (receipt : ∀ d x,x∈occurrences P r d→
      total x=localFee x+((childList P x).map total).sum)
    (terminal : occurrences P r (H+1)=[]) :
    total r=∑ j∈Finset.range (H+1),levelBill P r localFee j := by
  have h := telescoping_ledger (levelBill P r total) (levelBill P r localFee)
    (fun d=>ledger_step P r total localFee d (receipt d)) (H+1)
  simpa only [levelBill,show occurrences P r 0=[r] from rfl,terminal,List.map_nil,
    List.map_cons,List.sum_cons,List.sum_nil,Nat.add_zero] using h

theorem childList_bill_as_sum (P : FinitePlan X) (x : X) (fee : X→ℕ) :
    ((childList P x).map fee).sum=
      @Finset.sum (P.Slot x) ℕ _ (@Finset.univ _ (P.finiteSlot x)) (fee∘P.child x) := by
  classical
  letI : Fintype (P.Slot x) := P.finiteSlot x
  change (((Finset.univ : Finset (P.Slot x)).toList.map (P.child x)).map fee).sum=_
  rw [List.map_map,←List.sum_toFinset _ (Finset.nodup_toList _)]
  simp

#print axioms next_level_bill
#print axioms occurrence_tree_ledger
#print axioms childList_bill_as_sum
end J6R24MeteredRecursion

