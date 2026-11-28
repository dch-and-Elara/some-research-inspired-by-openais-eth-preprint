import J6R68ActiveInputsBaseGrid

/-! A raw valuation filter for every real offset word. Its output is
a unary register of exact valuation, or none for the center zero.
It never decodes an integer or calls padicValInt in the byte loop. -/
namespace J6R68ActiveInputs
open AOracleMachineTime P1DyadicGrid

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 10500000
set_option maxRecDepth 2800
set_option Elab.async false

def sameLengthTape : List Bool → List Bool → Meter Bool
  | [],[]=>⟨true,3⟩
  | _::x,_::y=>let q := sameLengthTape x y; ⟨q.result,q.steps+5⟩
  | _,_=>⟨false,3⟩

theorem same_length_tape_exact (x y : List Bool) :
    ((sameLengthTape x y).result=true ↔ x.length=y.length) ∧
      (sameLengthTape x y).steps ≤ 5*x.length+3 := by
  induction x generalizing y with
  | nil => cases y <;> simp [sameLengthTape]
  | cons b x ih =>
    cases y with
    | nil => simp [sameLengthTape]
    | cons c y =>
      obtain ⟨read,fee⟩ := ih y
      simp only [sameLengthTape,List.length_cons,Nat.add_right_cancel_iff]
      exact ⟨read,by omega⟩

def rawSignedLevel (axis bits : List Bool) : Meter (Option (List Bool)) :=
  let seek := walkToFirstOne bits
  match seek.result with
  | none=>⟨some axis,seek.steps+3⟩
  | some z=>
    let m := sameLengthTape z axis
    ⟨if m.result then none else some z,seek.steps+m.steps+5⟩

private theorem bits_value_false_head (k : ℕ) (rest : List Bool) :
    bitsValue (List.replicate k false++rest)=2^k*bitsValue rest := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [List.replicate_succ,List.cons_append,bitsValue,Bool.toNat_false,zero_add,ih,pow_succ]
    ring

private theorem cast_prefix (z rest : List Bool) (flat : z=List.replicate z.length false) :
    (bitsValue (z++rest) : ℤ)=pow₂ z.length*(bitsValue rest:ℤ) := by
  have e : bitsValue (z++rest)=2^z.length*bitsValue rest :=
    (congrArg (fun xs=>bitsValue (xs++rest)) flat).trans (bits_value_false_head _ _)
  rw [e,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  rfl

private theorem true_head_odd (rest : List Bool) : Odd (bitsValue (true::rest):ℤ) := by
  refine ⟨(bitsValue rest:ℤ),?_⟩
  simp only [bitsValue,Bool.toNat_true,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  omega

theorem signed_prefix_level (a : ℕ) (z rest : List Bool)
    (flat : z=List.replicate z.length false) (lo : z.length<a) :
    offsetCentre a (z++true::rest)≠0 ∧
      padicValInt 2 (offsetCentre a (z++true::rest))=z.length := by
  let k := z.length
  let n := (bitsValue (true::rest):ℤ)
  have hodd : Odd n := true_head_odd rest
  have diff : 0<a-k := by unfold k; omega
  have even : Even (pow₂ (a-k)) := by
    have h : a-k=(a-k-1)+1 := by omega
    rw [h,pow₂_succ]
    exact even_iff_two_dvd.mpr ⟨pow₂ (a-k-1),mul_comm _ _⟩
  have oddDiff : Odd (n-pow₂ (a-k)) :=
    Int.odd_sub.mpr ⟨fun _=>even,fun _=>hodd⟩
  have factor : pow₂ a=pow₂ k*pow₂ (a-k) := by
    unfold pow₂
    rw [←pow_add,Nat.add_sub_of_le lo.le]
  have h : offsetCentre a (z++true::rest)=pow₂ k*(n-pow₂ (a-k)) := by
    unfold offsetCentre
    rw [cast_prefix z (true::rest) flat,factor]
    change pow₂ k*n-pow₂ k*pow₂ (a-k)=_
    ring
  rw [h]
  exact ⟨mul_ne_zero (ne_of_gt (pow₂_pos k)) (odd_int_ne_zero oddDiff),
    valuation_pow₂_mul_odd k oddDiff⟩

theorem signed_raw_valuation_is_exact (a : ℕ) (axis xs : List Bool)
    (ax : axis.length=a) (width : xs.length=a+1) :
    let t := offsetCentre a xs
    let r := rawSignedLevel axis xs
    (match r.result with
      | none=>t=0
      | some ys=>t≠0 ∧ ys.length=padicValInt 2 t) ∧ r.steps ≤ 10*(a+1)+11 := by
  have shape := first_one_prefix_has_exact_shape xs
  have scan := actual_first_one_scan_fee xs
  cases e : (walkToFirstOne xs).result with
  | none =>
    rw [e] at shape
    have val : bitsValue xs=0 := by
      calc
        bitsValue xs=bitsValue (List.replicate xs.length false++[]) := by rw [List.append_nil,←shape]
        _=0 := by rw [bits_value_false_head]; simp [bitsValue]
    have den : offsetCentre a xs=pow₂ a*(-1) := by simp [offsetCentre,val]
    dsimp only [rawSignedLevel]
    rw [e]
    dsimp only
    refine ⟨?_,by omega⟩
    change offsetCentre a xs≠0 ∧ axis.length=padicValInt 2 (offsetCentre a xs)
    rw [den,ax,valuation_pow₂_mul_odd _ (by decide : Odd (-1:ℤ))]
    exact ⟨mul_ne_zero (ne_of_gt (pow₂_pos a)) (by decide),rfl⟩
  | some z =>
    rw [e] at shape
    obtain ⟨flat,rest,split⟩ := shape
    have w := congrArg List.length split
    rw [width,List.length_append,List.length_cons] at w
    have cap : z.length ≤ a := by omega
    obtain ⟨check,fee⟩ := same_length_tape_exact z axis
    dsimp only [rawSignedLevel]
    rw [e]
    dsimp only
    by_cases same : z.length=a
    · have y : rest=[] := List.length_eq_zero_iff.mp (by omega)
      have valid : offsetCentre a xs=0 := by
        rw [split,y]
        unfold offsetCentre
        rw [cast_prefix z [true] flat,same]
        simp [bitsValue,Bool.toNat]
      rw [if_pos (check.mpr (same.trans ax.symm))]
      exact ⟨valid,by omega⟩
    · have lo : z.length<a := by omega
      have mark := signed_prefix_level a z rest flat lo
      have diff : (sameLengthTape z axis).result≠true := by
        intro bad
        exact same ((check.mp bad).trans ax)
      rw [if_neg diff]
      exact ⟨by rw [split]; exact ⟨mark.1,mark.2.symm⟩,by omega⟩

#print axioms same_length_tape_exact
#print axioms signed_prefix_level
#print axioms signed_raw_valuation_is_exact
end J6R68ActiveInputs
