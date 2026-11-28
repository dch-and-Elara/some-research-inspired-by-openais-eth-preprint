import J6R50ModeDispatchCore
import J6R48DFSModeDrain
import J6R27OriginalGateModeCompare

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 9200000

/-! Run the verified halt-driven source cursor with a physical mode
counter and sparse-update register. The reference list is proof-only.
An ordinal is not charged as if an arbitrary typed lookup computed it. -/
namespace J6R50ModeDispatch
open AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply J6R48DFS
open J6R27OriginalGate

variable {q n tm : ℕ} {A : Type*}

def numberedStep (a : ℕ) (roster : List (RawMode q))
    (step : A  →  OpenMode q tm  →  Meter A) (before : A × Word tm) (raw : List (Word q)) :
    Meter (A × Word tm) :=
  let p := prepareMode a roster raw before.2
  match p.result with
  | none => ⟨before,p.steps+4⟩
  | some o =>
    let go := step before.1 o
    ⟨(go.result,o.next),p.steps+go.steps+4⟩

theorem numbered_step_advances (a : ℕ) (roster : List (RawMode q))
    (step : A  →  OpenMode q tm  →  Meter A) (before : A × Word tm) (raw : List (Word q))
    (len : roster.length=raw.length) (ht : 0<tm) (fit : before.2.val+1<2^tm) :
    ((numberedStep a roster step before raw).result.2).val=before.2.val+1 := by
  obtain ⟨v,h,_⟩ := prepare_emitted_mode_exact a roster raw before.2 len ht fit
  unfold numberedStep
  dsimp only
  rw [v]
  exact h

theorem numbered_fold_counter (a : ℕ) (roster : List (RawMode q))
    (step : A  →  OpenMode q tm  →  Meter A) (xs : List (List ℕ)) (before : A × Word tm)
    (len : ∀ v∈xs,v.length=roster.length) (ht : 0<tm) (fit : before.2.val+xs.length<2^tm) :
    ((foldExpected (numberedStep a roster step) xs before).result.2).val=before.2.val+xs.length := by
  induction xs generalizing before with
  | nil => simp [foldExpected]
  | cons raw rest ih =>
    let next := numberedStep a roster step before (raw.map word)
    have cap : before.2.val+1<2^tm := by simp only [List.length_cons] at fit; omega
    have x := numbered_step_advances a roster step before (raw.map word)
      (by rw [List.length_map]; exact (len raw List.mem_cons_self).symm) ht cap
    change next.result.2.val=before.2.val+1 at x
    have nxt : next.result.2.val+rest.length<2^tm := by
      rw [x]
      simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm 1] using fit
    have tail := ih next.result (fun v h=>len v (List.mem_cons_of_mem _ h)) nxt
    change (foldExpected (numberedStep a roster step) rest next.result).result.2.val=_
    rw [tail,x,List.length_cons]
    omega

def countedDrain (a : ℕ) (roster : List (RawMode q))
    (step : A  →  OpenMode q tm  →  Meter A) (P : Pending q n) (seed : A) (fee : ℕ) :
    Meter ((A × Word tm) × Bool) :=
  let zero := copyFixed (word (q:=tm) 0)
  modeDrain (numberedStep a roster step) P (seed,zero.result) (fee+zero.steps)

theorem counted_real_drain_starts_zero (a : ℕ) (roster : List (RawMode q))
    (step : A  →  OpenMode q tm  →  Meter A) (P : Pending q n) (seed : A) (fee : ℕ)
    (xs : List (List ℕ)) (trace : Runs n P.state xs (.ascend []))
    (len : ∀ v∈xs,v.length=roster.length) (ht : 0<tm) (fit : xs.length<2^tm) :
    let out := countedDrain a roster step P seed fee
    out.result.2=true ∧ out.result.1.2.val=xs.length ∧
      out.steps ≤ fee+(3*tm+1)+
        (foldExpected (numberedStep a roster step) xs (seed,word (q:=tm) 0)).steps+
        (xs.length+1)*delayCap q n := by
  let zero := copyFixed (word (q:=tm) 0)
  have x : zero.result=word (q:=tm) 0 := congrArg Meter.result (copy_fixed_exact (word (q:=tm) 0))
  have c : zero.steps=3*tm+1 := congrArg Meter.steps (copy_fixed_exact (word (q:=tm) 0))
  have z : (word (q:=tm) 0).val=0 := word_val (Nat.pow_pos (by decide))
  obtain ⟨v,hcost⟩ := halt_driven_fold_exact P xs trace
    (numberedStep a roster step) (seed,zero.result) (fee+zero.steps)
  have k := numbered_fold_counter a roster step xs (seed,word (q:=tm) 0) len ht
    (by simpa only [z,zero_add] using fit)
  simp only [countedDrain]
  rw [show copyFixed (word (q:=tm) 0)=zero from rfl,v]
  rw [x,c] at hcost
  refine ⟨rfl,by simpa only [x,z,zero_add] using k,?_⟩
  rw [x,c]
  exact hcost

#print axioms numberedStep
#print axioms numbered_step_advances
#print axioms numbered_fold_counter
#print axioms counted_real_drain_starts_zero
end J6R50ModeDispatch

