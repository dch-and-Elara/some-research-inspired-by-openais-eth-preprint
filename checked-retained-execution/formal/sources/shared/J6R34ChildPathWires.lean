import J6R34ChildPathPorts

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 11000000

/-! A paid translator from an actual serialized edge order and live
lineage headers to the WireRead ABI. An ordinal is not foreknown:
the program emits one unary tick for each mismatching fixed word. -/
namespace J6R34ChildPath
open scoped Classical Polynomial
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor

def seekLane {w : ℕ} (seek : Word w) : List (Word w)→Meter (Option (List Bool))
  | [] => ⟨none,2⟩
  | head::tail =>
    let test := cmpAddr seek head
    if test.result then ⟨some [],test.steps+8⟩
    else
      let advance := seekLane seek tail
      ⟨advance.result.map (true::·),test.steps+advance.steps+8⟩

def seekStride (w : ℕ) : ℕ := 10*w+13

theorem seek_at_real_position {w : ℕ} (keys : List (Word w)) (nodup : keys.Nodup)
    (j : Fin keys.length) :
    seekLane keys[j.val] keys=⟨some (List.replicate j.val true),(j.val+1)*seekStride w⟩ := by
  induction keys with
  | nil => exact Fin.elim0 j
  | cons x xs ih =>
    cases j using Fin.cases with
    | zero =>
      change seekLane x (x::xs)=⟨some [],1*seekStride w⟩
      simp only [seekLane,(cmpAddr_exact x x).1.mpr rfl,if_true,(cmpAddr_exact x x).2,
        seekStride,one_mul]
    | succ j =>
      have tailProps := (List.nodup_cons.mp nodup)
      have miss : xs[j.val]≠x := fun E=>tailProps.1 (E ▸ List.getElem_mem j.isLt)
      have test : (cmpAddr xs[j.val] x).result=false :=
        Bool.eq_false_iff.mpr (fun H=>miss ((cmpAddr_exact _ _).1.mp H))
      have h := ih tailProps.2 j
      change seekLane xs[j.val] (x::xs)=
        ⟨some (List.replicate (j.val+1) true),((j.val+1)+1)*seekStride w⟩
      simp only [seekLane,test,if_neg Bool.false_ne_true,(cmpAddr_exact _ _).2,h,Option.map_some,
        List.replicate_succ,Nat.add_mul,Nat.one_mul]
      congr 1
      unfold seekStride
      omega

structure WireRequest (w : ℕ) where
  incumbent : Word w
  ancestry : List Bool

def emitWire {w : ℕ} (keys : List (Word w)) (req : WireRequest w) : Meter (Option WireRead) :=
  let u := seekLane req.incumbent keys
  let h := copyBytes req.ancestry
  ⟨u.result.map (fun lane=>⟨h.result,lane⟩),u.steps+h.steps+5⟩

def emitWires {w : ℕ} (keys : List (Word w)) : List (WireRequest w)→Meter (Option (List WireRead))
  | [] => ⟨some [],4⟩
  | req::rest =>
    let this := emitWire keys req
    match this.result with
    | none => ⟨none,this.steps+4⟩
    | some row =>
      let tail := emitWires keys rest
      ⟨tail.result.map (row::·),this.steps+tail.steps+4⟩

def sourceWireFee (w pos h : ℕ) :=
  (pos+1)*seekStride w+3*h+10

theorem emit_wire_at_source_order {w M : ℕ}
    (keys : List (Word w)) (keyFn : Fin M→Word w) (keyInj : Function.Injective keyFn)
    (keyOrder : keys=List.ofFn keyFn) (j : Fin M) (header : List Bool) :
    emitWire keys ⟨keyFn j,header⟩=
      ⟨some ⟨header,List.replicate j.val true⟩,sourceWireFee w j.val header.length-4⟩ := by
  subst keys
  have h : (List.ofFn keyFn).Nodup := List.nodup_ofFn.mpr keyInj
  let n : Fin (List.ofFn keyFn).length := Fin.cast List.length_ofFn.symm j
  have find := seek_at_real_position (List.ofFn keyFn) h n
  rw [List.getElem_ofFn] at find
  change seekLane (keyFn j) (List.ofFn keyFn)=
    ⟨some (List.replicate j.val true),(j.val+1)*seekStride w⟩ at find
  unfold emitWire
  dsimp only
  rw [find,copyBytes_exact]
  simp only [Option.map_some,sourceWireFee]
  congr 1

/-- Runtime wire production uses the raw request list and actual edge
words. The order and headers on the right are correctness receipts;
the runtime never maps a noncomputable logical trace to bytes as an oracle. -/
theorem source_wire_tape {V : Type*} {w M : ℕ}
    (keys : List (Word w)) (keyFn : Fin M→Word w) (keyInj : Function.Injective keyFn)
    (keyOrder : keys=List.ofFn keyFn)
    (ports : List V) (header : V→List Bool) (ordinal : V→Fin M)
    (incoming : List (WireRequest w))
    (receipt : incoming=ports.map (fun u=>⟨keyFn (ordinal u),header u⟩)) :
    let run := emitWires keys incoming
    run.result=some (ports.map (fun u=>⟨header u,List.replicate (ordinal u).val true⟩)) ∧
      run.steps=4+(ports.map (fun u=>sourceWireFee w (ordinal u).val (header u).length)).sum := by
  subst incoming
  induction ports with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih =>
    obtain ⟨h1,h2⟩ := ih
    have h := emit_wire_at_source_order keys keyFn keyInj keyOrder (ordinal x) (header x)
    simp only [List.map_cons,emitWires,h,h1,h2,Option.map_some,List.sum_cons,true_and]
    have P : 4≤sourceWireFee w (ordinal x).val (header x).length := by unfold sourceWireFee; omega
    omega

#print axioms seek_at_real_position
#print axioms emit_wire_at_source_order
#print axioms source_wire_tape
end J6R34ChildPath
