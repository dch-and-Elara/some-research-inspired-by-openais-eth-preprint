import J6R22ActiveScaled
import A1R12Words

/-! Paid reading of one high word after certified common dyadic
clearing. The machine checks the actual low bits before removing
them. This is one scalar coordinate, not the computation of its
weighted numerator or a whole-register assembly claim. -/
namespace J6R22Active
open A1R10 A1R12 AOracleMachineTime AOracleMachineTimeTape

theorem bitsValue_drop (n : ℕ) (xs : List Bool) :
    bitsValue (xs.drop n)=bitsValue xs/(2^n) := by
  induction n generalizing xs with
  | zero => simp
  | succ n ih =>
    cases xs with
    | nil => simp [bitsValue]
    | cons x xs =>
      change bitsValue (xs.drop n)=(x.toNat+2*bitsValue xs)/2^(n+1)
      rw [ih,pow_succ,Nat.mul_comm _ 2,←Nat.div_div_eq_div_mul]
      have hb : x.toNat≤1 := by cases x <;> decide
      have hs : (x.toNat+2*bitsValue xs)/2=bitsValue xs := by omega
      rw [hs]

theorem lowBits_eq_take (B : ℕ) (xs : List Bool) (h : B≤xs.length) :
    lowBits B xs=xs.take B := by
  induction B generalizing xs with
  | zero => rfl
  | succ B ih =>
    cases xs with
    | nil => simp at h
    | cons x xs =>
      simp only [List.length_cons,Nat.succ_le_succ_iff] at h
      simp only [lowBits,List.take_succ_cons,ih xs h]

theorem all_zero_iff_value_zero (xs : List Bool) :
    xs.all (fun b=>!b)=true ↔ bitsValue xs=0 := by
  induction xs with
  | nil => simp [bitsValue]
  | cons b xs ih =>
    cases b
    · simp [bitsValue,ih]
    · simp [bitsValue]

def highWord (p B : ℕ) (x : Word (p+B)) : Meter (Option (Word p)) :=
  let h := (x.val.take B).all (fun b=>!b)
  if h then
    let y : Word p := ⟨x.val.drop B,by simp only [List.length_drop,x.property]; omega⟩
    ⟨some y,8*(p+B+1)+4⟩
  else ⟨none,8*(p+B+1)+4⟩

theorem highWord_exact (p B : ℕ) (x : Word (p+B)) :
    let y := highWord p B x
    y.steps=8*(p+B+1)+4 ∧
    ((∃ w, y.result=some w) ↔ 2^B∣bitsValue x.val) ∧
    (∀ w,y.result=some w→bitsValue w.val=bitsValue x.val/2^B) := by
  let low := x.val.take B
  have hlo : bitsValue low=bitsValue x.val%2^B := by
    change bitsValue (x.val.take B)=_
    rw [←lowBits_eq_take B x.val (by rw [x.property]; omega),lowBits_value]
  have hb : low.all (fun b=>!b)=true ↔ 2^B∣bitsValue x.val := by
    rw [all_zero_iff_value_zero,hlo,Nat.dvd_iff_mod_eq_zero]
  dsimp only
  by_cases h : low.all (fun b=>!b)=true
  · unfold highWord
    rw [if_pos h]
    refine ⟨rfl,⟨fun _=>hb.mp h,fun _=>⟨_,rfl⟩⟩,?_⟩
    intro w eq
    obtain rfl := Option.some.inj eq
    exact bitsValue_drop B x.val
  · unfold highWord
    rw [if_neg h]
    refine ⟨rfl,?_,?_⟩
    · constructor
      · rintro ⟨w,e⟩
        cases e
      · intro hd
        exact False.elim (h (hb.mpr hd))
    · intro w eq
      cases eq

theorem highWord_on_scaled_register (p B out : ℕ) (x : Word (p+B))
    (h : wordRead x=(2:NativeProbeRing.Base (p+B))^B*out) :
    ∃ w, (highWord p B x).result=some w ∧ bitsValue w.val=out%2^p ∧
      (highWord p B x).steps=8*(p+B+1)+4 := by
  have hv : (wordRead x).val=bitsValue x.val := by
    change ((bitsValue x.val:ℕ):ZMod (2^(p+B))).val=_
    have hl : bitsValue x.val<2^(p+B) := by
      simpa only [x.property] using bitsValue_lt x.val
    exact ZMod.val_natCast_of_lt hl
  have H := high_word_requires_exact_divisibility p B out
  dsimp only at H
  rw [←h,hv] at H
  obtain ⟨w,hw⟩ := (highWord_exact p B x).2.1.mpr H.1
  exact ⟨w,hw,((highWord_exact p B x).2.2 w hw).trans H.2,(highWord_exact p B x).1⟩

#print axioms bitsValue_drop
#print axioms highWord_exact
#print axioms highWord_on_scaled_register
end J6R22Active



