
import J6ChildPlan
import A1R12Combine

/-! An actual depth-first Boolean edge enumeration, not a leaf oracle or
a materialized list of all assignments. At each visit the accumulated
reverse bit chain is physically reversed once; every callback cost is kept
in the accumulated meter. Ring operations are the native U/V bit kernels. -/
namespace J6R21Leaf
open scoped BigOperators
open AOracleMachineTime AOracleCoordinates A1R10 A1R11 A1R12
set_option linter.unusedSectionVars false

variable {p ell : ℕ} {fw : List (A1R10.Word p)}

/-- One literal forward scan of the reverse edge-bit tape at a leaf. -/
def reverseFee (n : ℕ) : ℕ := 3*n+2

def enumerate (hp : 0<p) (read : List Bool→Meter (UVBlock fw ell)) :
    ℕ → List Bool → Meter (UVBlock fw ell)
  | 0,rev => padCost (read rev.reverse) (reverseFee rev.length)
  | n+1,rev => padCost (addM hp (enumerate hp read n (false::rev))
      (enumerate hp read n (true::rev))) 4

theorem packed_cons (b : Bool) {n : ℕ} (x : Fin n→Bool) :
    List.ofFn (Fin.cons b x) = b :: List.ofFn x := by
  rw [List.ofFn_succ]
  simp only [Fin.cons_zero,Fin.cons_succ]

theorem enumerate_exact (hp : 0<p) (read : List Bool→Meter (UVBlock fw ell))
    (n : ℕ) (rev : List Bool) :
    uvRead hp fw ell (enumerate hp read n rev).result =
      J6ChildPlan.allBits n (fun x =>
        uvRead hp fw ell (read (rev.reverse++List.ofFn x)).result) := by
  induction n generalizing rev with
  | zero => simp [enumerate,J6ChildPlan.allBits,padCost]
  | succ n ih =>
    simp only [enumerate,padCost,addM_read,J6ChildPlan.allBits,ih,
      List.reverse_cons,packed_cons,List.append_assoc,List.singleton_append]

/-- This sum counts each original callback exactly once for every
assignment visiting it, including repeated reads of identical local keys. -/
def callbackTotal (read : List Bool→Meter (UVBlock fw ell))
    (n : ℕ) (rev : List Bool) : ℕ :=
  J6ChildPlan.allBits n (fun x => (read (rev.reverse++List.ofFn x)).steps)

theorem callbackTotal_split (read : List Bool→Meter (UVBlock fw ell))
    (n : ℕ) (rev : List Bool) :
    callbackTotal read (n+1) rev =
      callbackTotal read n (false::rev)+callbackTotal read n (true::rev) := by
  simp only [callbackTotal,J6ChildPlan.allBits,packed_cons,List.reverse_cons,
    List.append_assoc,List.singleton_append]

def innerFee (e ell p : ℕ) (hp : 0<p) : ℕ := addCap e ell p hp+6

theorem enumerate_bills_callbacks (hp : 0<p) (read : List Bool→Meter (UVBlock fw ell))
    (n : ℕ) (rev : List Bool) :
    let billed := callbackTotal read n rev
    let work := (enumerate hp read n rev).steps
    billed ≤ work ∧
      work ≤ billed+2^n*reverseFee (rev.length+n)+(2^n-1)*innerFee fw.length ell p hp := by
  dsimp only
  induction n generalizing rev with
  | zero =>
    simp [enumerate,callbackTotal,J6ChildPlan.allBits,padCost]
  | succ n ih =>
    let l := enumerate hp read n (false::rev)
    let r := enumerate hp read n (true::rev)
    let L := callbackTotal read n (false::rev)
    let R := callbackTotal read n (true::rev)
    let count := 2^n
    let fee := reverseFee (rev.length+(n+1))
    let add := innerFee fw.length ell p hp
    have plen (b : Bool) : (b::rev).length+n=rev.length+(n+1) := by simp; omega
    have hl : L≤l.steps ∧ l.steps≤L+count*fee+(count-1)*add := by
      simpa only [l,L,count,fee,add,plen] using ih (false::rev)
    have hr : R≤r.steps ∧ r.steps≤R+count*fee+(count-1)*add := by
      simpa only [r,R,count,fee,add,plen] using ih (true::rev)
    have q : 0<count := by unfold count; positivity
    have hCount : 2^(n+1)=count+count := by rw [pow_succ]; unfold count; omega
    have hInner : 2^(n+1)-1=(count-1)+(count-1)+1 := by rw [hCount]; omega
    rw [callbackTotal_split,hInner,hCount]
    change L+R ≤ (padCost (addM hp l r) 4).steps ∧
      (padCost (addM hp l r) 4).steps≤L+R+(count+count)*fee+((count-1)+(count-1)+1)*add
    constructor
    · exact (Nat.add_le_add hl.1 hr.1).trans (by simp [padCost,addM]; omega)
    · have b : (padCost (addM hp l r) 4).steps≤l.steps+r.steps+add := by
        have m := addM_cost hp l r
        change (addM hp l r).steps+4 ≤ l.steps+r.steps+(addCap fw.length ell p hp+6)
        omega
      rw [Nat.add_mul,Nat.add_mul,Nat.add_mul,one_mul]
      omega

theorem callback_at_complete_assignment (read : List Bool→Meter (UVBlock fw ell)) (n : ℕ) :
    callbackTotal read n [] = ∑ x : Fin n→Bool, (read (List.ofFn x)).steps := by
  simp only [callbackTotal,List.reverse_nil,List.nil_append,J6ChildPlan.allBits_exact]

/-- Exact number of independent edge assignments, not a factor of 64 or
a count of source vertices. -/
theorem leaf_assignment_count (n : ℕ) :
    (∑ _ : Fin n→Bool, (1:ℕ)) = 2^n := by
  rw [← J6ChildPlan.allBits_exact]
  exact J6ChildPlan.allBits_visits n

#print axioms packed_cons
#print axioms enumerate_exact
#print axioms callbackTotal_split
#print axioms enumerate_bills_callbacks
#print axioms callback_at_complete_assignment
#print axioms leaf_assignment_count
end J6R21Leaf
