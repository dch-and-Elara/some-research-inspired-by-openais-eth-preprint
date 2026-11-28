import J6R25PreparedSupplyPorts

/-! Expose one cut of the *existing* non-tail-recursive selectPorts,
without changing its output or Meter. A copied body is pending even
when its comparison is false: the original let-bound read precedes
the recursive call. The suffix is already selected at this cut.
The observation is not a claim about physical heap or its own cost. -/
namespace J6R68.MountFilterScratch
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply

set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 5000000

structure SelectionCut (w : ℕ) where
  pending : List (List Bool×Bool)
  selected : List (PortRow w)

def pendingOperand {w : ℕ} (key : Word 6) (r : PortRow w) : List Bool×Bool :=
  ((copyBytes r.body).result,(cmpAddr key r.group).result)

def observeSelection {w : ℕ} (key : Word 6) :
    ℕ→List (PortRow w)→Meter (List (PortRow w))×SelectionCut w
  | 0,xs =>
    let done := selectPorts key xs
    (done,⟨[],done.result⟩)
  | _+1,[] =>
    let done := selectPorts key []
    (done,⟨[],done.result⟩)
  | j+1,x::xs =>
    let put := copyBytes x.body
    let test := cmpAddr key x.group
    let inner := observeSelection key j xs
    let answer := if test.result then {x with body := put.result}::inner.1.result else inner.1.result
    (⟨answer,inner.1.steps+put.steps+test.steps+2*w+15⟩,
      ⟨(put.result,test.result)::inner.2.pending,inner.2.selected⟩)

theorem observed_projection_is_the_literal_selector {w : ℕ}
    (key : Word 6) (j : ℕ) (xs : List (PortRow w)) :
    (observeSelection key j xs).1=selectPorts key xs := by
  induction j generalizing xs with
  | zero => rfl
  | succ j ih =>
    cases xs with
    | nil => rfl
    | cons x xs => simp only [observeSelection,selectPorts,ih]

theorem physical_selector_cut_keeps_exact_disjoint_slices {w : ℕ}
    (key : Word 6) (j : ℕ) (xs : List (PortRow w)) :
    let seen := (observeSelection key j xs).2
    seen.pending=(xs.take j).map (pendingOperand key) ∧
      seen.selected=(selectPorts key (xs.drop j)).result := by
  induction j generalizing xs with
  | zero => exact ⟨rfl,rfl⟩
  | succ j ih =>
    cases xs with
    | nil => exact ⟨rfl,rfl⟩
    | cons x xs =>
      have got := ih xs
      dsimp only [observeSelection,List.take_succ_cons,List.drop_succ_cons,List.map_cons] at got ⊢
      exact ⟨congrArg ((pendingOperand key x)::·) got.1,got.2⟩

def pendingCopiedBits (xs : List (List Bool×Bool)) : ℕ :=
  (xs.map (fun x=>x.1.length+1)).sum

def SelectionCut.namedPayloadBits {w : ℕ} (x : SelectionCut w)
    (encode : PortRow w→List Bool) : ℕ :=
  pendingCopiedBits x.pending+(x.selected.flatMap encode).length

private theorem flatMap_length_by_rows {w : ℕ} (xs : List (PortRow w))
    (encode : PortRow w→List Bool) :
    (xs.flatMap encode).length=(xs.map (fun x=>(encode x).length)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,List.length_append,List.map_cons,List.sum_cons,ih]

private theorem copied_width_by_rows {w : ℕ} (key : Word 6) (xs : List (PortRow w)) :
    pendingCopiedBits (xs.map (pendingOperand key))=
      (xs.map (fun x=>x.body.length+1)).sum := by
  unfold pendingCopiedBits
  rw [List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro x _
  simp only [Function.comp_apply,pendingOperand,copyBytes_exact]

private theorem prefix_copies_fit_prefix {w : ℕ} (key : Word 6)
    (xs : List (PortRow w)) (encode : PortRow w→List Bool)
    (fit : ∀ x,x.body.length+1 ≤ (encode x).length) :
    pendingCopiedBits (xs.map (pendingOperand key)) ≤ (xs.flatMap encode).length := by
  rw [copied_width_by_rows,flatMap_length_by_rows]
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons]
    exact Nat.add_le_add (fit x) ih

private theorem selected_output_fits_suffix {w : ℕ}
    (xs : List (PortRow w)) (accept : PortRow w→Bool) (encode : PortRow w→List Bool) :
    ((xs.filter accept).flatMap encode).length ≤ (xs.flatMap encode).length := by
  induction xs with
  | nil => exact le_rfl
  | cons x xs ih =>
    cases good : accept x
    · simp only [List.filter_cons,good,Bool.false_eq_true,if_false,List.flatMap_cons,List.length_append]
      exact ih.trans (Nat.le_add_left _ _)
    · simp only [List.filter_cons,good,if_true,List.flatMap_cons,List.length_append]
      exact Nat.add_le_add_left ih _

theorem pending_copies_and_selected_suffix_fit_the_disjoint_source
    {w : ℕ} (key : Word 6) (j : ℕ) (xs : List (PortRow w))
    (encode : PortRow w→List Bool)
    (fit : ∀ x,x.body.length+1 ≤ (encode x).length) :
    ((observeSelection key j xs).2).namedPayloadBits encode ≤ (xs.flatMap encode).length := by
  obtain ⟨p,s⟩ := physical_selector_cut_keeps_exact_disjoint_slices key j xs
  unfold SelectionCut.namedPayloadBits
  rw [p,s,(select_ports_exact key (xs.drop j)).1]
  have left := prefix_copies_fit_prefix key (xs.take j) encode fit
  have right := selected_output_fits_suffix (xs.drop j) (fun row=>(cmpAddr key row.group).result) encode
  refine (Nat.add_le_add left right).trans_eq ?_
  rw [←List.length_append,←List.flatMap_append,List.take_append_drop]

#print axioms observed_projection_is_the_literal_selector
#print axioms physical_selector_cut_keeps_exact_disjoint_slices
#print axioms pending_copies_and_selected_suffix_fit_the_disjoint_source
end J6R68.MountFilterScratch
