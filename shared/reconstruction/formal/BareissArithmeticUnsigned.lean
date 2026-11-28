import AffineCostBits

/-!
Binary long division over the existing little-endian Boolean words.
The program uses one borrow pass for each dividend bit. Mathematical
natural-number operations appearing in the statements are correctness
specifications, and the counters annotate Boolean-cell operations.
-/

namespace Reconstruction.BareissArithmetic

open AffineCost.Bit

private def borrowBit (a b c : Bool) : Bool := (!a && (b || c)) || (b && c)

private theorem full_subtractor (a b c : Bool) :
    digit (sumBit a b c) + digit b + digit c = digit a + 2 * digit (borrowBit a b c) := by
  cases a <;> cases b <;> cases c <;> decide

/-- Fixed-width subtraction with a final borrow. The fuel is a list, so
the payload needs no arithmetic loop counter. -/
private def borrowPass : List Unit → Bool → Word → Word → Run (Word × Bool)
  | [], c, _, _ => ⟨([], c), 8⟩
  | _ :: n, c, xs, ys =>
    let a := xs.headD false
    let b := ys.headD false
    let r := borrowPass n (borrowBit a b c) xs.tail ys.tail
    ⟨(sumBit a b c :: r.value.1, r.value.2), 32 + r.steps⟩

private theorem borrowPass_steps (n : List Unit) (c : Bool) (xs ys : Word) :
    (borrowPass n c xs ys).steps = 32 * n.length + 8 := by
  induction n generalizing c xs ys with
  | nil => rfl
  | cons z n ih => simp only [borrowPass, List.length_cons, ih]; omega

private theorem borrowPass_length (n : List Unit) (c : Bool) (xs ys : Word) :
    (borrowPass n c xs ys).value.1.length = n.length := by
  induction n generalizing c xs ys <;> simp [borrowPass, *]

private theorem borrowPass_value (n : List Unit) (c : Bool) (xs ys : Word) :
    let r := (borrowPass n c xs ys).value
    value r.1 + value (ys.take n.length) + digit c =
      value (xs.take n.length) + 2 ^ n.length * digit r.2 := by
  induction n generalizing c xs ys with
  | nil => simp [borrowPass]
  | cons z n ih =>
    simp only [borrowPass, value_cons, List.length_cons, value_take, pow_succ]
    have h₁ := full_subtractor (xs.headD false) (ys.headD false) c
    have h₂ := ih (borrowBit (xs.headD false) (ys.headD false) c) xs.tail ys.tail
    dsimp at h₂
    simp only [Nat.mul_assoc, Nat.mul_comm] at *
    omega

/-- Subtract unsigned words with zero extension. The flag says that the
minuend was smaller. In that case the word is the wrapped difference. -/
def trialSub (xs ys : Word) : Run (Word × Bool) :=
  let n := fuel xs ys
  let r := borrowPass n false xs ys
  let t := trim r.value.1
  ⟨(t.value, r.value.2), 16 + 8 * (n.length + 1) + r.steps + t.steps⟩

theorem trialSub_steps (xs ys : Word) :
    (trialSub xs ys).steps ≤ 64 * (xs.length + ys.length + 1) := by
  simp only [trialSub, borrowPass_steps, trim_steps, borrowPass_length, fuel_length]
  have h : max xs.length ys.length ≤ xs.length + ys.length := max_le (by omega) (by omega)
  omega

theorem trialSub_tight (xs ys : Word) : Tight (trialSub xs ys).value.1 := trim_tight _

private theorem trialSub_value (xs ys : Word) :
    let r := (trialSub xs ys).value
    value r.1 + value ys = value xs + 2 ^ (max xs.length ys.length) * digit r.2 := by
  have h := borrowPass_value (fuel xs ys) false xs ys
  dsimp at h
  simpa only [trialSub, trim_value, fuel_length, List.take_of_length_le (le_max_left _ _),
    List.take_of_length_le (le_max_right _ _), digit, Bool.false_eq_true, if_false, Nat.add_zero]
    using h

theorem trialSub_borrow (xs ys : Word) :
    (trialSub xs ys).value.2 = true ↔ value xs < value ys := by
  let r := (trialSub xs ys).value
  have he : value r.1 + value ys = value xs + 2 ^ (max xs.length ys.length) * digit r.2 :=
    trialSub_value xs ys
  have ht : value r.1 < 2 ^ (max xs.length ys.length) := by
    have H := value_lt (borrowPass (fuel xs ys) false xs ys).value.1
    simpa only [r, trialSub, trim_value, borrowPass_length, fuel_length] using H
  change r.2 = true ↔ _
  cases hr : r.2
  · have hv : value r.1 + value ys = value xs := by simpa [hr, digit] using he
    simp only [Bool.false_eq_true, false_iff]
    omega
  · have hv : value r.1 + value ys = value xs + 2 ^ (max xs.length ys.length) := by
      simpa [hr, digit] using he
    simp only [true_iff]
    omega

theorem trialSub_noBorrow {xs ys : Word} (h : (trialSub xs ys).value.2 = false) :
    value (trialSub xs ys).value.1 + value ys = value xs := by
  simpa only [h, digit, Bool.false_eq_true, if_false, Nat.mul_zero, Nat.add_zero]
    using trialSub_value xs ys

theorem tight_eq_nil_iff {w : Word} (h : Tight w) : w = [] ↔ value w = 0 := by
  constructor
  · rintro rfl
    rfl
  · intro hw
    rcases h with h | h
    · exact h
    · have hp : 0 < (2 : ℕ) ^ (w.length - 1) := by positivity
      omega

/-- Process the high part first, then shift the remainder by one bit and
try to subtract the divisor. The quotient word carries one cell per input
bit until the final trim. -/
private def divideAux (y : Word) : Word → Run (Word × Word)
  | [] => ⟨([], []), 8⟩
  | b :: xs =>
    let r := divideAux y xs
    let z := b :: r.value.2
    let s := trialSub z y
    if s.value.2 then
      let t := trim z
      ⟨(false :: r.value.1, t.value), 16 + r.steps + s.steps + t.steps⟩
    else ⟨(true :: r.value.1, s.value.1), 16 + r.steps + s.steps⟩

private theorem divideAux_invariant (y xs : Word) (hy : 0 < value y) :
    let r := (divideAux y xs).value
    value xs = value y * value r.1 + value r.2 ∧
      value r.2 < value y ∧ Tight r.2 ∧ r.1.length = xs.length := by
  induction xs with
  | nil => simp [divideAux, hy, Tight]
  | cons b xs ih =>
    let r := (divideAux y xs).value
    let z := b :: r.2
    let s := (trialSub z y).value
    change value xs = value y * value r.1 + value r.2 ∧
      value r.2 < value y ∧ Tight r.2 ∧ r.1.length = xs.length at ih
    have hz : value z = digit b + 2 * value r.2 := rfl
    have hzmax : value z < 2 * value y := by
      have hb := digit_le b
      omega
    have hrEq : (divideAux y xs).value = r := rfl
    have hzEq : b :: r.2 = z := rfl
    have hsEq : (trialSub z y).value = s := rfl
    cases hs : s.2 with
    | true =>
      have hlt : value z < value y := (trialSub_borrow z y).mp hs
      simp only [divideAux, hrEq, hzEq, hsEq, hs, if_true, value_cons, trim_value,
        List.length_cons, ih.2.2.2, and_true]
      change digit b + 2 * value xs = value y * (digit false + 2 * value r.1) + value z ∧
        value z < value y ∧ Tight (trim z).value
      refine ⟨?_, hlt, trim_tight _⟩
      rw [show digit false = 0 from rfl, Nat.zero_add, Nat.mul_left_comm (value y) 2]
      omega
    | false =>
      have hsub : value s.1 + value y = value z := trialSub_noBorrow hs
      simp only [divideAux, hrEq, hzEq, hsEq, hs, Bool.false_eq_true, if_false, value_cons,
        List.length_cons, ih.2.2.2, and_true]
      change digit b + 2 * value xs = value y * (digit true + 2 * value r.1) + value s.1 ∧
        value s.1 < value y ∧ Tight s.1
      refine ⟨?_, by omega, trialSub_tight _ _⟩
      rw [show digit true = 1 from rfl, Nat.mul_add, Nat.mul_one, Nat.mul_left_comm (value y) 2]
      omega

private theorem divideAux_steps (y xs : Word) (hy : 0 < value y) :
    (divideAux y xs).steps ≤ 256 * (xs.length + 1) * (y.length + 1) := by
  induction xs with
  | nil => simp [divideAux]; omega
  | cons b xs ih =>
    let r := divideAux y xs
    let z := b :: r.value.2
    let s := trialSub z y
    have hInv := divideAux_invariant y xs hy
    have hr : r.value.2.length ≤ y.length :=
      length_le_of_tight hInv.2.2.1 (hInv.2.1.trans (value_lt y))
    have hz : z.length ≤ y.length + 1 := by dsimp [z]; omega
    have hSub := trialSub_steps z y
    have hTrim := trim_steps z
    have hStep : 16 + s.steps + (trim z).steps ≤ 256 * (y.length + 1) := by
      dsimp only [s]
      omega
    have ih' : r.steps ≤ 256 * (xs.length + 1) * (y.length + 1) := ih
    have hs : (divideAux y (b :: xs)).steps ≤ r.steps + 256 * (y.length + 1) := by
      have hrEq : divideAux y xs = r := rfl
      have hzEq : b :: r.value.2 = z := rfl
      have hsEq : trialSub z y = s := rfl
      by_cases h : s.value.2 = true <;>
        simp only [divideAux, hrEq, hzEq, hsEq, h, if_true, if_false, Bool.false_eq_true] <;> omega
    refine hs.trans ((Nat.add_le_add_right ih' _).trans_eq ?_)
    simp only [List.length_cons]
    ring

/-- Return a trimmed quotient exactly when the divisor is nonzero and the
remainder is zero. No numerical division is used by the payload. -/
def exactDivWord (xs ys : Word) : Run (Option Word) :=
  let y := trim ys
  if y.value.isEmpty then ⟨none, 16 + y.steps⟩
  else
    let r := divideAux y.value xs
    if r.value.2.isEmpty then
      let q := trim r.value.1
      ⟨some q.value, 16 + y.steps + r.steps + q.steps⟩
    else ⟨none, 16 + y.steps + r.steps⟩

theorem exactDivWord_sound {xs ys q : Word} (h : (exactDivWord xs ys).value = some q) :
    0 < value ys ∧ value xs = value ys * value q ∧ Tight q ∧ q.length ≤ xs.length := by
  dsimp only [exactDivWord] at h
  split at h
  · simp at h
  next hy =>
    let y := (trim ys).value
    have hy' : 0 < value y := by
      apply Nat.pos_of_ne_zero
      intro hz
      exact hy (List.isEmpty_iff.mpr ((tight_eq_nil_iff (trim_tight ys)).mpr hz))
    let r := (divideAux y xs).value
    have hInv := divideAux_invariant y xs hy'
    change value xs = value y * value r.1 + value r.2 ∧
      value r.2 < value y ∧ Tight r.2 ∧ r.1.length = xs.length at hInv
    split at h
    next hr =>
      have hq : (trim r.1).value = q := Option.some.inj h
      have hr' : r.2 = [] := List.isEmpty_iff.mp hr
      rw [← hq]
      have hv : value y = value ys := trim_value ys
      have he : value xs = value y * value r.1 := by
        simpa only [hr', value_nil, Nat.add_zero] using hInv.1
      exact ⟨hv ▸ hy', by rw [trim_value, ← hv]; exact he, trim_tight _,
        (trim_length _).trans_eq hInv.2.2.2⟩
    next => simp at h

theorem exactDivWord_complete {xs ys : Word} (hy : 0 < value ys)
    (hd : value ys ∣ value xs) : ∃ q, (exactDivWord xs ys).value = some q := by
  let y := (trim ys).value
  have hy' : 0 < value y := by simpa only [y, trim_value] using hy
  have hny : y.isEmpty = false := by
    cases hb : y.isEmpty
    · rfl
    · have hh := List.isEmpty_iff.mp hb
      simp only [hh, value_nil, lt_irrefl] at hy'
  let r := (divideAux y xs).value
  have hInv := divideAux_invariant y xs hy'
  have hrem : value r.2 = 0 := by
    have hmod : value xs % value y = value r.2 := by
      rw [hInv.1, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hInv.2.1]
    have hz : value xs % value y = 0 := Nat.mod_eq_zero_of_dvd (by
      simpa only [y, trim_value] using hd)
    exact hmod.symm.trans hz
  have hr : r.2.isEmpty = true := List.isEmpty_iff.mpr ((tight_eq_nil_iff hInv.2.2.1).mpr hrem)
  refine ⟨(trim r.1).value, ?_⟩
  simp only [exactDivWord, ← show y = (trim ys).value from rfl, hny, Bool.false_eq_true,
    if_false, ← show r = (divideAux y xs).value from rfl, hr, if_true]

theorem exactDivWord_steps (xs ys : Word) :
    (exactDivWord xs ys).steps ≤ 512 * (xs.length + 1) * (ys.length + 1) := by
  let y := (trim ys).value
  have hY : y.length ≤ ys.length := trim_length _
  have hTy := trim_steps ys
  have hA : 16 + (trim ys).steps ≤ 32 * (ys.length + 1) := by omega
  have hBase : 32 * (ys.length + 1) ≤ 32 * (xs.length + 1) * (ys.length + 1) := by
    have H := Nat.mul_le_mul_right (ys.length + 1) (show 32 ≤ 32 * (xs.length + 1) by omega)
    exact H
  dsimp only [exactDivWord]
  split
  · exact hA.trans (hBase.trans (by
      apply Nat.mul_le_mul_right
      exact Nat.mul_le_mul_right _ (by decide : 32 ≤ 512)))
  next hy =>
    have hpos : 0 < value y := by
      apply Nat.pos_of_ne_zero
      intro hz
      exact hy (List.isEmpty_iff.mpr ((tight_eq_nil_iff (trim_tight ys)).mpr hz))
    have hR := (divideAux_steps y xs hpos).trans
      (Nat.mul_le_mul_left _ (Nat.add_le_add_right hY 1))
    let r := (divideAux y xs).value
    have hq : r.1.length = xs.length := (divideAux_invariant y xs hpos).2.2.2
    have hT : (trim r.1).steps ≤ 8 * (xs.length + 1) := by rw [trim_steps, hq]
    have hT' : 8 * (xs.length + 1) ≤ 8 * (xs.length + 1) * (ys.length + 1) := by
      exact Nat.le_mul_of_pos_right _ (by omega)
    have hb : 32 * (xs.length + 1) * (ys.length + 1) +
        256 * (xs.length + 1) * (ys.length + 1) +
        8 * (xs.length + 1) * (ys.length + 1) ≤ 512 * (xs.length + 1) * (ys.length + 1) := by
      calc
        _ = 296 * (xs.length + 1) * (ys.length + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide))
    dsimp only [y, r] at hR hT
    split <;> dsimp only <;> omega

end Reconstruction.BareissArithmetic
