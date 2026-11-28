import J6R27OriginalGateModeCompare
import Mathlib.Data.List.NodupEquivFin

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7200000

/-! Paid replay of the legacy *tuple-order* catalogue, distinct from
the resident variable roster. It does not assume old and current tuple
orders agree, and it does not create the old file for free. -/
namespace J6R51Dispatch
open scoped Classical
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate

variable {q tm : ℕ}

def compareDense : List (Word q) → List (Word q) → Meter Bool
  | [],[] => ⟨true,2⟩
  | [],_::_ => ⟨false,2⟩
  | _::_,[] => ⟨false,2⟩
  | x::xs,y::ys =>
    let h := cmpAddr x y
    let t := compareDense xs ys
    ⟨h.result && t.result,h.steps+t.steps+4⟩

theorem dense_comparison_exact (x y : List (Word q)) :
    ((compareDense x y).result=true ↔ x=y) ∧
      (compareDense x y).steps ≤ 2+x.length*(10*q+9) := by
  induction x generalizing y with
  | nil => cases y <;> simp [compareDense]
  | cons u us ih => 
    cases y with
    | nil => simp [compareDense]
    | cons v vs =>
      have h := ih vs
      have c := cmpAddr_exact u v
      constructor
      · simp only [compareDense,Bool.and_eq_true,c.1,h.1,List.cons.injEq]
      · change (cmpAddr u v).steps+(compareDense us vs).steps+4 ≤
          2+(us.length+1)*(10*q+9)
        rw [c.2,Nat.add_mul,Nat.one_mul]
        omega

def scanPrevious (query : List (Word q)) :
    List (List (Word q)) → Word tm → Meter (Option (Word tm))
  | [],_ => ⟨none,3⟩
  | row::tail,clock =>
    let hit := compareDense query row
    if hit.result then
      let out := copyFixed clock
      ⟨some out.result,hit.steps+out.steps+4⟩
    else
      let inc := increment clock
      let rest := scanPrevious query tail inc.result
      ⟨rest.result,hit.steps+inc.steps+rest.steps+6⟩

theorem scan_previous_returns_index (query : List (Word q)) (file : List (List (Word q)))
    (clock : Word tm) (ht : 0<tm) (fit : clock.val+file.length<2^tm) (existsHere : query∈file) :
    let run := scanPrevious query file clock
    run.result=some (word (clock.val+file.idxOf query)) ∧
      run.steps≤3+file.length*(query.length*(10*q+9)+13*tm+12) := by
  induction file generalizing clock with
  | nil => simp at existsHere
  | cons row tail ih =>
    have h := dense_comparison_exact query row
    by_cases same : query=row
    · subst row
      have b : (compareDense query query).result=true := h.1.mpr rfl
      simp only [scanPrevious,b,if_true,copy_fixed_exact,List.idxOf_cons_self,Nat.add_zero]
      refine ⟨congrArg some (valued_word clock).symm,?_⟩
      change (compareDense query query).steps+(3*tm+1)+4 ≤
        3+(tail.length+1)*(query.length*(10*q+9)+13*tm+12)
      rw [Nat.add_mul,Nat.one_mul]
      omega
    · have b : (compareDense query row).result≠true := fun m=>same (h.1.mp m)
      have cap : clock.val+1<2^tm := by simp only [List.length_cons] at fit; omega
      obtain ⟨ic,icost⟩ := increment_exact ht clock cap
      have rest : query∈tail := (List.mem_cons.mp existsHere).resolve_left same
      have room : (increment clock).result.val+tail.length<2^tm := by
        rw [ic]; simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using fit
      obtain ⟨rr,cost⟩ := ih (increment clock).result room rest
      rw [scanPrevious,if_neg b]
      dsimp only
      refine ⟨?_,?_⟩
      · rw [rr,ic]
        have reversed : row≠query := fun e=>same e.symm
        have bits : (row == query)=false := Bool.eq_false_iff.mpr (fun hit=>reversed (beq_iff_eq.mp hit))
        simp [List.idxOf_cons,bits,Nat.add_assoc,Nat.add_comm 1]
      · change (compareDense query row).steps+(increment clock).steps+
          (scanPrevious query tail (increment clock).result).steps+6 ≤
          3+(tail.length+1)*(query.length*(10*q+9)+13*tm+12)
        rw [icost,Nat.add_mul,Nat.one_mul]
        omega

def readPriorOrdinal (query : List (Word q)) (file : List (List (Word q))) :
    Meter (Option (Word tm)) :=
  let init := copyFixed (word (q:=tm) 0)
  let out := scanPrevious query file init.result
  ⟨out.result,init.steps+out.steps+3⟩

theorem read_prior_ordinal_correct (query : List (Word q)) (file : List (List (Word q)))
    (ht : 0<tm) (fit : file.length<2^tm) (here : query∈file) :
    (readPriorOrdinal (tm:=tm) query file).result=some (word (file.idxOf query)) ∧
    (readPriorOrdinal (tm:=tm) query file).steps≤
      3*tm+7+file.length*(query.length*(10*q+9)+13*tm+12) := by
  have hz : (word (q:=tm) 0).val=0 := word_val (Nat.pow_pos (by decide))
  obtain ⟨r,c⟩ := scan_previous_returns_index query file (word (q:=tm) 0) ht
    (by simpa only [hz,zero_add] using fit) here
  simp only [readPriorOrdinal,copy_fixed_exact,r,hz,zero_add,true_and]
  omega

#print axioms dense_comparison_exact
#print axioms scan_previous_returns_index
#print axioms read_prior_ordinal_correct
end J6R51Dispatch

