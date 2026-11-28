import J6R22ActiveJet

/-! Named numeric arrays of one actual dense multiplication coalescence.
This is a payload observer, not a modification of the gates or evaluator.
Counting both aliases as separate copies gives a conservative bound. -/
namespace J6R50NonModeScratch
open A1R10 AOracleMachineTime
set_option autoImplicit false
set_option warningAsError true

variable {A R : Type*}

def encodeArrays (enc : A→List Bool) (xs : List (List A)) : List Bool :=
  xs.flatMap (fun row=>row.flatMap enc)

theorem flat_payload_exact (enc : A→List Bool) (w : ℕ)
    (codes : ∀ x,(enc x).length=w) (xs : List A) :
    (xs.flatMap enc).length=xs.length*w := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons,List.length_append,codes,ih,List.length_cons,Nat.succ_mul,Nat.add_comm]

theorem arrays_payload_exact (enc : A→List Bool) (w : ℕ)
    (codes : ∀ x,(enc x).length=w) (xs : List (List A)) :
    (encodeArrays enc xs).length=(xs.map List.length).sum*w := by
  induction xs with
  | nil => simp [encodeArrays]
  | cons x xs ih =>
    change (x.flatMap enc ++ encodeArrays enc xs).length=
      (x.length+(xs.map List.length).sum)*w
    rw [List.length_append,flat_payload_exact enc w codes x,ih,Nat.add_mul]

def combineArrays (g : Gates A) (x : A) (xs ys : List A) : List (List A) :=
  let lo := convolve g xs ys
  let hi := timesRow g x ys
  let row := g.zero::(hi.result ++ zeros g xs.length)
  let prev := g.zero::lo.result
  let out := addRows g row prev
  [lo.result,hi.result,row,prev,out.result]

theorem combine_arrays_actual_output (g : Gates A) (x : A) (xs ys : List A) :
    (combineArrays g x xs ys).getLast?=some (convolve g (x::xs) ys).result := rfl

theorem combine_arrays_lengths [CommRing R] (o : Ops A R)
    (x : A) (xs ys : List A) :
    (combineArrays o.toGates x xs ys).map List.length =
      [xs.length+ys.length,ys.length,
        xs.length+ys.length+1,xs.length+ys.length+1,xs.length+ys.length+1] := by
  let lo := convolve o.toGates xs ys
  let hi := timesRow o.toGates x ys
  let row := o.zero::(hi.result ++ zeros o.toGates xs.length)
  let prev := o.zero::lo.result
  have hLo : lo.result.length=xs.length+ys.length := (convolve_exact o xs ys).1
  have hHi : hi.result.length=ys.length := (timesRow_exact o x ys).1
  have hRow : row.length=xs.length+ys.length+1 := by
    simp only [row,List.length_cons,List.length_append,hHi,zeros_len]
    omega
  have hPrev : prev.length=xs.length+ys.length+1 := by
    simp only [prev,List.length_cons,hLo]
  have hOut : (addRows o.toGates row prev).result.length=xs.length+ys.length+1 :=
    (addRows_exact o row prev (hRow.trans hPrev.symm)).1.trans hRow
  change [lo.result.length,hi.result.length,row.length,prev.length,
    (addRows o.toGates row prev).result.length]=_
  rw [hLo,hHi,hRow,hPrev,hOut]

theorem actual_combine_payload_bound [CommRing R] (o : Ops A R)
    (enc : A→List Bool) (w : ℕ) (codes : ∀ x,(enc x).length=w)
    (x : A) (xs ys : List A) :
    (encodeArrays enc (combineArrays o.toGates x xs ys)).length ≤
      (5*((x::xs).length+ys.length))*w := by
  rw [arrays_payload_exact enc w codes,combine_arrays_lengths]
  apply Nat.mul_le_mul_right
  simp only [List.sum_cons,List.sum_nil,List.length_cons]
  omega

/-- One selected unwind stage down the same physical first-operand
suffix, with the unchanged second operand. Input words, scalar-gate
scratch and continuation metadata are outside these five arrays. -/
theorem suffix_combine_payload_bound [CommRing R] (o : Ops A R)
    (enc : A→List Bool) (w : ℕ) (codes : ∀ x,(enc x).length=w)
    (pref : List A) (x : A) (xs ys : List A) :
    (encodeArrays enc (combineArrays o.toGates x xs ys)).length ≤
      (5*((pref++(x::xs)).length+ys.length))*w := by
  apply (actual_combine_payload_bound o enc w codes x xs ys).trans
  apply Nat.mul_le_mul_right
  simp only [List.length_append,List.length_cons]
  omega

#print axioms flat_payload_exact
#print axioms arrays_payload_exact
#print axioms combine_arrays_actual_output
#print axioms combine_arrays_lengths
#print axioms actual_combine_payload_bound
#print axioms suffix_combine_payload_bound
end J6R50NonModeScratch
