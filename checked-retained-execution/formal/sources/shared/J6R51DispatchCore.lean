import J6R27OriginalGateDense

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7400000

/-! Charged reindexing across physical variable-roster order. Unlike
R27 densify, this scans for the exact serialized mode key and therefore
does not assume the sparse support is a subsequence in the target order. -/
namespace J6R51Dispatch
open AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R27OriginalGate

variable {q : ℕ}

def readExponent (k : RawMode q) : List (RawMode q × Word q) → Meter (Word q)
  | [] => let z := copyFixed (word (q:=q) 0); ⟨z.result,z.steps+1⟩
  | (j,e)::xs =>
    let test := cmpMode k j
    if test.result then
      let copy := copyFixed e
      ⟨copy.result,test.steps+copy.steps+4⟩
    else
      let rem := readExponent k xs
      ⟨rem.result,test.steps+rem.steps+4⟩

def compareCharge (k : RawMode q) : ℕ :=
  5*k.key.1.length+5*k.key.2.length+30*q+35

theorem sparse_read_cost (k : RawMode q) (sp : List (RawMode q × Word q)) :
    (readExponent k sp).steps ≤ 3*q+2+sp.length*compareCharge k := by
  induction sp with
  | nil => simp [readExponent,copy_fixed_exact]
  | cons x xs ih =>
    rcases x with ⟨j,e⟩
    have h := (cmp_mode_exact k j).2
    simp only [readExponent]
    split
    · rw [copy_fixed_exact]
      change (cmpMode k j).steps+(3*q+1)+4 ≤ 3*q+2+(xs.length+1)*compareCharge k
      rw [Nat.add_mul,one_mul]
      unfold compareCharge
      omega
    · change (cmpMode k j).steps+(readExponent k xs).steps+4 ≤ 3*q+2+(xs.length+1)*compareCharge k
      rw [Nat.add_mul,one_mul]
      unfold compareCharge at ih ⊢
      omega

theorem exact_sparse_read_from_source (k : RawMode q) (source : List (RawMode q))
    (value : RawMode q → Word q) (hit : (value k).val=0 ∨ k∈source) :
    (readExponent k (supportSpec source (source.map value))).result=value k := by
  induction source with
  | nil =>
    have zero : (value k).val=0 := by simpa using hit
    simp only [List.map_nil,supportSpec,List.zip_nil_right,List.filter_nil,readExponent,copy_fixed_exact]
    exact (congrArg word zero).symm.trans (valued_word _)
  | cons j rem ih =>
    rw [List.map_cons,support_cons_if]
    by_cases zero : (value j).val=0
    · rw [if_pos zero]
      apply ih
      rcases hit with hz | hk
      · exact Or.inl hz
      · rcases List.mem_cons.mp hk with e | h
        · exact Or.inl (e.symm ▸ zero)
        · exact Or.inr h
    · rw [if_neg zero,readExponent]
      by_cases e : k=j
      · subst j
        rw [if_pos ((cmp_mode_exact k k).1.mpr rfl),copy_fixed_exact]
      · have neq : (cmpMode k j).result≠true := fun h=>e ((cmp_mode_exact k j).1.mp h)
        rw [if_neg neq]
        apply ih
        exact hit.imp id (fun h=>(List.mem_cons.mp h).resolve_left e)

def replayDense (sp : List (RawMode q × Word q)) : List (RawMode q) → Meter (List (Word q))
  | [] => ⟨[],2⟩
  | k::ks =>
    let here := readExponent k sp
    let rest := replayDense sp ks
    ⟨here.result::rest.result,here.steps+rest.steps+5⟩

theorem replay_across_literal_rosters (source target : List (RawMode q))
    (value : RawMode q → Word q) (cover : ∀ k∈target,k∈source) :
    (replayDense (supportSpec source (source.map value)) target).result=target.map value := by
  induction target with
  | nil => rfl
  | cons k ks ih =>
    have head := exact_sparse_read_from_source k source value (Or.inr (cover k List.mem_cons_self))
    have tail := ih (fun j h=>cover j (List.mem_cons_of_mem _ h))
    simp only [replayDense,List.map_cons,head,tail]

theorem replay_actual_scan_fee (sp : List (RawMode q × Word q)) (target : List (RawMode q))
    (B : ℕ) (fits : ∀ k∈target,compareCharge k ≤ B) :
    (replayDense sp target).steps ≤ 2+target.length*(3*q+7+sp.length*B) := by
  induction target with
  | nil => simp [replayDense]
  | cons k ks ih =>
    have tail := ih (fun j h=>fits j (List.mem_cons_of_mem _ h))
    have head := (sparse_read_cost k sp).trans (Nat.add_le_add_left
      (Nat.mul_le_mul_left sp.length (fits k List.mem_cons_self)) _)
    change (readExponent k sp).steps+(replayDense sp ks).steps+5 ≤
      2+(ks.length+1)*(3*q+7+sp.length*B)
    rw [Nat.add_mul,Nat.one_mul]
    omega

#print axioms readExponent
#print axioms sparse_read_cost
#print axioms exact_sparse_read_from_source
#print axioms replay_across_literal_rosters
#print axioms replay_actual_scan_fee
end J6R51Dispatch

