import J6R51DispatchOrdinal

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 7700000

/-! An explicit installed route bank can implement the discovery
interface without computing a typed Finsupp mode. Each comparison is
a paid binary comparison against the currently offered raw words.
The Eq transport in the successful branch is proof erasure, not a
change of the offered words or a source of an unpriced route. -/
namespace J6R54Dispatch
open AOracleMachineTime J6R15ModeCost J6R51Dispatch

variable {q : ℕ} {C : List (Word q)→Type*}
local notation "Entry" => (Σ bs : List (Word q), C bs)

def lookupBytes (raw : List (Word q)) : List Entry→Meter (Option (C raw))
  | [] => ⟨none,2⟩
  | row::rest =>
    let cmp := compareDense raw row.1
    if h : cmp.result=true then
      let e : raw=row.1 := (dense_comparison_exact raw row.1).1.mp h
      ⟨some (e.symm ▸ row.2),cmp.steps+3⟩
    else
      let out := lookupBytes raw rest
      ⟨out.result,cmp.steps+out.steps+4⟩

def prefixLookupFee (raw : List (Word q)) (earlier : List Entry) : ℕ :=
  (earlier.map (fun row=>(compareDense raw row.1).steps+4)).sum

theorem prior_rows_are_paid_then_exact_same_carrier
    (raw : List (Word q)) (value : C raw) (earlier later : List Entry)
    (before : ∀ e∈earlier,e.1≠raw) :
    lookupBytes raw (earlier++⟨raw,value⟩::later) =
      ⟨some value,prefixLookupFee raw earlier+(compareDense raw raw).steps+3⟩ := by
  induction earlier with
  | nil =>
    have h : (compareDense raw raw).result=true := (dense_comparison_exact raw raw).1.mpr rfl
    simp only [List.nil_append,lookupBytes,h,dif_pos,prefixLookupFee,List.map_nil,List.sum_nil,zero_add]
  | cons row prev ih =>
    have q : (compareDense raw row.1).result≠true :=
      fun yes=>(before row List.mem_cons_self) ((dense_comparison_exact raw row.1).1.mp yes).symm
    have tail := ih (fun e h=>before e (List.mem_cons_of_mem _ h))
    simp only [List.cons_append,lookupBytes,dif_neg q,tail,prefixLookupFee,
      List.map_cons,List.sum_cons]
    congr 1
    omega

theorem first_carrier_search_bound (raw : List (Word q)) (value : C raw)
    (earlier later : List Entry) (before : ∀ e∈earlier,e.1≠raw) :
    (lookupBytes raw (earlier++⟨raw,value⟩::later)).steps≤
      (earlier.length+1)*(raw.length*(10*q+9)+6) := by
  have parts : prefixLookupFee raw earlier ≤ earlier.length*(raw.length*(10*q+9)+6) := by
    unfold prefixLookupFee
    induction earlier with
    | nil => simp
    | cons h tail ih =>
      have step := (dense_comparison_exact raw h.1).2
      have rest := ih (fun e he=>before e (List.mem_cons_of_mem _ he))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  rw [prior_rows_are_paid_then_exact_same_carrier raw value earlier later before]
  simp only [Nat.add_mul,Nat.one_mul]
  have final := (dense_comparison_exact raw raw).2
  omega

#print axioms lookupBytes
#print axioms prior_rows_are_paid_then_exact_same_carrier
#print axioms first_carrier_search_bound
end J6R54Dispatch

