import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace AffineCost.Bit

/-- Measured bit programs. The natural-number counter is a proof annotation;
the payload algorithms only traverse lists and operate on Boolean cells. -/
structure Run (α : Type) where
  value : α
  steps : ℕ

abbrev Word := List Bool

def digit (b : Bool) : ℕ := if b then 1 else 0

def value : Word → ℕ
  | [] => 0
  | b :: bs => digit b + 2 * value bs

@[simp] theorem value_nil : value [] = 0 := rfl
@[simp] theorem value_cons (b : Bool) (bs : Word) : value (b :: bs) = digit b + 2 * value bs := rfl

theorem digit_le (b : Bool) : digit b ≤ 1 := by cases b <;> decide

theorem value_lt (xs : Word) : value xs < 2 ^ xs.length := by
  induction xs with
  | nil => decide
  | cons b xs ih =>
    simp only [List.length_cons, pow_succ, value_cons]
    have := digit_le b
    omega

theorem value_take (xs : Word) (n : ℕ) :
    value (xs.take (n+1)) = digit (xs.headD false) + 2 * value (xs.tail.take n) := by
  cases xs
  · simp [digit]
  · rfl

/-- Discard redundant high zero cells. -/
def trim : Word → Run Word
  | [] => ⟨[], 8⟩
  | b :: bs =>
    let r := trim bs
    let z := if r.value.isEmpty && !b then [] else b :: r.value
    ⟨z, 8 + r.steps⟩

theorem trim_steps (xs : Word) : (trim xs).steps = 8*(xs.length+1) := by
  induction xs <;> simp [trim, *, Nat.mul_add, Nat.add_comm]

theorem trim_length (xs : Word) : (trim xs).value.length ≤ xs.length := by
  induction xs with
  | nil => decide
  | cons b bs ih =>
    simp only [trim]
    split <;> simp_all

theorem trim_value (xs : Word) : value (trim xs).value = value xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    simp only [trim]
    split
    next h =>
      simp only [Bool.and_eq_true] at h
      obtain ⟨he,hb⟩ := h
      have hz := List.isEmpty_iff.mp he
      rw [hz] at ih
      have hb' : b = false := by cases b <;> simp_all
      simp [ih.symm, digit, hb']
    next => rw [value_cons, value_cons, ih]

def Tight (xs : Word) : Prop := xs = [] ∨ 2^(xs.length-1) ≤ value xs

theorem cons_tight_of_cons {xs : Word} (h : Tight xs) (hn : xs ≠ []) (b : Bool) :
    Tight (b::xs) := by
  have hp := h.resolve_left hn
  have hLen : 0 < xs.length := List.length_pos_iff.mpr hn
  have he : 2^(xs.length) = 2^(xs.length-1)*2 := by
    rw [← pow_succ, show xs.length-1+1 = xs.length by omega]
  right
  simp only [List.length_cons, Nat.add_sub_cancel, value_cons]
  omega

theorem trim_tight (xs : Word) : Tight (trim xs).value := by
  induction xs with
  | nil => exact Or.inl rfl
  | cons b bs ih =>
    simp only [trim]
    split
    next => exact Or.inl rfl
    next h =>
      by_cases he : (trim bs).value = []
      · cases b
        · simp [he] at h
        · rw [he]
          exact Or.inr (by decide)
      · exact cons_tight_of_cons ih he b

theorem length_le_of_tight {xs : Word} (ht : Tight xs) {n : ℕ} (hv : value xs < 2^n) :
    xs.length ≤ n := by
  rcases ht with rfl | ht
  · simp
  · by_contra! h
    have he : 2^n ≤ 2^(xs.length-1) := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (by omega)
    omega

/-- Full-adder cells use only Boolean operations. -/
def sumBit (a b c : Bool) : Bool := xor (xor a b) c
def carryBit (a b c : Bool) : Bool := (a && b) || ((a || b) && c)

theorem full_adder (a b c : Bool) :
    digit (sumBit a b c) + 2 * digit (carryBit a b c) = digit a + digit b + digit c := by
  cases a <;> cases b <;> cases c <;> decide

/-- Unary fuel for one pass over two bit strings. No arithmetic is needed
to obtain the loop bound. -/
def fuel : Word → Word → List Unit
  | [], ys => ys.map fun _ => ()
  | _ :: xs, ys => () :: fuel xs ys.tail

theorem fuel_length (xs ys : Word) : (fuel xs ys).length = max xs.length ys.length := by
  induction xs generalizing ys with
  | nil => simp [fuel]
  | cons x xs ih =>
    cases ys with
    | nil => simp [fuel, ih]
    | cons y ys =>
      simp only [fuel, ih, List.tail_cons, List.length_cons]
      omega

/-- The step count charges the bit gates, cell reads and cell writes in each
ripple iteration, with a constant allowance for branching and the base case. -/
def ripple : List Unit → Bool → Word → Word → Run Word
  | [], c, _, _ => ⟨[c], 8⟩
  | _ :: n, c, xs, ys =>
    let a := xs.headD false
    let b := ys.headD false
    let r := ripple n (carryBit a b c) xs.tail ys.tail
    ⟨sumBit a b c :: r.value, 32 + r.steps⟩

theorem ripple_steps (n : List Unit) (c : Bool) (xs ys : Word) :
    (ripple n c xs ys).steps = 32*n.length+8 := by
  induction n generalizing c xs ys with
  | nil => rfl
  | cons x n ih => simp [ripple, ih, Nat.mul_succ]; omega

theorem ripple_length (n : List Unit) (c : Bool) (xs ys : Word) :
    (ripple n c xs ys).value.length = n.length+1 := by
  induction n generalizing c xs ys <;> simp [ripple, *]

theorem ripple_value (n : List Unit) (c : Bool) (xs ys : Word) :
    value (ripple n c xs ys).value = value (xs.take n.length) + value (ys.take n.length) + digit c := by
  induction n generalizing c xs ys with
  | nil => simp [ripple, digit]
  | cons x n ih =>
    simp only [ripple, value_cons, ih, List.length_cons, value_take]
    have h := full_adder (xs.headD false) (ys.headD false) c
    omega

def add (xs ys : Word) : Run Word :=
  let n := fuel xs ys
  let r := ripple n false xs ys
  let t := trim r.value
  ⟨t.value, 16 + 8*(n.length+1) + r.steps + t.steps⟩

theorem add_value (xs ys : Word) : value (add xs ys).value = value xs + value ys := by
  simp [add, trim_value, ripple_value, fuel_length, List.take_of_length_le, digit]

theorem add_tight (xs ys : Word) : Tight (add xs ys).value := trim_tight _

theorem add_length (xs ys : Word) : (add xs ys).value.length ≤ max xs.length ys.length+1 :=
  (trim_length _).trans_eq ((ripple_length _ _ _ _).trans (by rw [fuel_length]))

theorem add_steps (xs ys : Word) : (add xs ys).steps ≤ 64*(xs.length+ys.length+1) := by
  simp only [add, ripple_steps, ripple_length, trim_steps, fuel_length]
  have : max xs.length ys.length ≤ xs.length+ys.length := max_le (by omega) (by omega)
  omega

def shift (xs : Word) : Word :=
  if xs.isEmpty then [] else false :: xs

theorem shift_value (xs : Word) : value (shift xs) = 2*value xs := by
  cases xs <;> simp [shift, digit]

theorem shift_tight {xs : Word} (h : Tight xs) : Tight (shift xs) := by
  cases xs
  · exact Or.inl rfl
  next b bs => exact cons_tight_of_cons h (by simp) false

theorem shift_length (xs : Word) : (shift xs).length ≤ xs.length+1 := by
  cases xs <;> simp [shift]

/-- Schoolbook multiplication with one shifted partial result per multiplier bit. -/
def mul (xs : Word) : Word → Run Word
  | [] => ⟨[], 8⟩
  | b :: bs =>
    let r := mul xs bs
    let y := shift r.value
    if b then
      let s := add xs y
      ⟨s.value, 16 + r.steps + s.steps⟩
    else ⟨y, 16 + r.steps⟩

theorem mul_value (xs ys : Word) : value (mul xs ys).value = value xs * value ys := by
  induction ys with
  | nil => simp [mul]
  | cons b bs ih =>
    cases b <;> simp [mul, shift_value, add_value, digit, ih] <;> ring

theorem mul_tight (xs ys : Word) : Tight (mul xs ys).value := by
  induction ys with
  | nil => exact Or.inl rfl
  | cons b bs ih =>
    cases b
    · exact shift_tight ih
    · exact add_tight _ _

theorem mul_length (xs ys : Word) : (mul xs ys).value.length ≤ xs.length+ys.length := by
  apply length_le_of_tight (mul_tight _ _)
  rw [mul_value, pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (value_lt xs) (value_lt ys)

theorem mul_steps (xs ys : Word) :
    (mul xs ys).steps ≤ 256*(ys.length+1)*(xs.length+ys.length+1) := by
  induction ys with
  | nil => simp [mul]; omega
  | cons b bs ih =>
    have hy : (shift (mul xs bs).value).length ≤ xs.length+bs.length+1 :=
      (shift_length _).trans (Nat.add_le_add_right (mul_length _ _) 1)
    have ha := add_steps xs (shift (mul xs bs).value)
    cases b <;> simp only [mul, Bool.false_eq_true, if_true, if_false,
      List.length_cons]
    all_goals
      calc
        _ ≤ 256*(bs.length+1)*(xs.length+bs.length+1) +
            256*(xs.length+bs.length+1) := by omega
        _ ≤ 256*(bs.length+1+1)*(xs.length+(bs.length+1)+1) := by
          rw [show 256*(bs.length+1)*(xs.length+bs.length+1) +
              256*(xs.length+bs.length+1) =
              256*(bs.length+1+1)*(xs.length+bs.length+1) by ring]
          exact Nat.mul_le_mul_left _ (by omega)

theorem value_inj_same {xs ys : Word} (hl : xs.length = ys.length)
    (hv : value xs = value ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons a xs ih =>
    cases ys with
    | nil => simp at hl
    | cons b ys =>
      have hb : a = b := by
        simp only [value_cons] at hv
        cases a <;> cases b <;> simp [digit] at hv ⊢ <;> omega
      subst b
      have hv' : value xs = value ys := by simp only [value_cons] at hv; omega
      exact congrArg (List.cons a) (ih (by simpa using hl) hv')

def compare : Word → Word → Run Bool
  | [], [] => ⟨true,8⟩
  | _ :: _, [] | [], _ :: _ => ⟨false,8⟩
  | a :: xs, b :: ys =>
    if a == b then
      let r := compare xs ys
      ⟨r.value,8+r.steps⟩
    else ⟨false,8⟩

theorem compare_spec (xs ys : Word) : (compare xs ys).value = true ↔ xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [compare]
  | cons a xs ih =>
    cases ys with
    | nil => simp [compare]
    | cons b ys =>
      by_cases h : a = b <;> simp [compare, beq_iff_eq, h, ih]

theorem compare_steps (xs ys : Word) : (compare xs ys).steps ≤ 8*(xs.length+ys.length+1) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [compare]
  | cons a xs ih =>
    cases ys with
    | nil => simp [compare]
    | cons b ys =>
      by_cases h : a = b
      · have := ih ys
        simp [compare, h]
        omega
      · simp [compare, beq_iff_eq,h]

def equal (xs ys : Word) : Run Bool :=
  let a := trim xs
  let b := trim ys
  let c := compare a.value b.value
  ⟨c.value, 8 + a.steps + b.steps + c.steps⟩

theorem equal_spec (xs ys : Word) : (equal xs ys).value = true ↔ value xs = value ys := by
  let x := (trim xs).value
  let y := (trim ys).value
  change (compare x y).value = true ↔ _
  rw [compare_spec]
  have hx : value x = value xs := trim_value _
  have hy : value y = value ys := trim_value _
  rw [← hx, ← hy]
  constructor
  · exact congrArg value
  · intro h
    apply value_inj_same _ h
    exact le_antisymm (length_le_of_tight (trim_tight xs) (h ▸ value_lt y))
      (length_le_of_tight (trim_tight ys) (h.symm ▸ value_lt x))

theorem equal_steps (xs ys : Word) : (equal xs ys).steps ≤ 32*(xs.length+ys.length+1) := by
  simp only [equal, trim_steps]
  have hx := trim_length xs
  have hy := trim_length ys
  have hc := compare_steps (trim xs).value (trim ys).value
  omega

end AffineCost.Bit
