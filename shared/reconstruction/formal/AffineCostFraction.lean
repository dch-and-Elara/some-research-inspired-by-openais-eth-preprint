import AffineCostBits
import Mathlib.Data.Rat.Cast.Order

namespace AffineCost.Bit

/-- Signed bit strings as a difference of unsigned magnitudes. Redundant
representatives are permitted, so evaluation requires no integer division. -/
structure Signed where
  plus : Word
  minus : Word

namespace Signed

def size (a : Signed) : ℕ := max a.plus.length a.minus.length
def number (a : Signed) : ℤ := (value a.plus : ℤ) - value a.minus

def neg (a : Signed) : Signed := ⟨a.minus, a.plus⟩

@[simp] theorem neg_number (a : Signed) : a.neg.number = -a.number := by
  simp only [neg, number]
  ring

@[simp] theorem neg_size (a : Signed) : a.neg.size = a.size := max_comm _ _

def add (a b : Signed) : Run Signed :=
  let p := Bit.add a.plus b.plus
  let n := Bit.add a.minus b.minus
  ⟨⟨p.value,n.value⟩, 8+p.steps+n.steps⟩

def mul (a b : Signed) : Run Signed :=
  let pp := Bit.mul a.plus b.plus
  let nn := Bit.mul a.minus b.minus
  let pn := Bit.mul a.plus b.minus
  let np := Bit.mul a.minus b.plus
  let p := Bit.add pp.value nn.value
  let n := Bit.add pn.value np.value
  ⟨⟨p.value,n.value⟩, 24+pp.steps+nn.steps+pn.steps+np.steps+p.steps+n.steps⟩

@[simp] theorem add_number (a b : Signed) : (add a b).value.number = a.number + b.number := by
  simp only [add, number, add_value, Nat.cast_add]
  ring

@[simp] theorem mul_number (a b : Signed) : (mul a b).value.number = a.number * b.number := by
  simp only [mul, number, add_value, mul_value, Nat.cast_add, Nat.cast_mul]
  ring

theorem add_size (a b : Signed) : (add a b).value.size ≤ max a.size b.size+1 := by
  have hp := Bit.add_length a.plus b.plus
  have hn := Bit.add_length a.minus b.minus
  simp only [add, size]
  omega

theorem mul_size (a b : Signed) : (mul a b).value.size ≤ a.size+b.size+1 := by
  have h₀ := Bit.mul_length a.plus b.plus
  have h₁ := Bit.mul_length a.minus b.minus
  have h₂ := Bit.mul_length a.plus b.minus
  have h₃ := Bit.mul_length a.minus b.plus
  have hp := Bit.add_length (Bit.mul a.plus b.plus).value (Bit.mul a.minus b.minus).value
  have hn := Bit.add_length (Bit.mul a.plus b.minus).value (Bit.mul a.minus b.plus).value
  simp only [mul, size]
  omega

theorem add_steps (a b : Signed) : (add a b).steps ≤ 144*(a.size+b.size+1) := by
  have hp := Bit.add_steps a.plus b.plus
  have hn := Bit.add_steps a.minus b.minus
  unfold add size
  have ha₀ := le_max_left a.plus.length a.minus.length
  have ha₁ := le_max_right a.plus.length a.minus.length
  have hb₀ := le_max_left b.plus.length b.minus.length
  have hb₁ := le_max_right b.plus.length b.minus.length
  dsimp
  omega

theorem mul_steps (a b : Signed) : (mul a b).steps ≤ 4096*(a.size+b.size+1)^2 := by
  let W := a.size+b.size+1
  have h (x y : Word) (hx : x.length ≤ a.size) (hy : y.length ≤ b.size) :
      (Bit.mul x y).steps ≤ 256*W*W := by
    apply (Bit.mul_steps _ _).trans
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (by dsimp [W]; omega))
      (by dsimp [W]; omega)
  have ha (xs ys : Word) (hx : xs.length ≤ W) (hy : ys.length ≤ W) :
      (Bit.add xs ys).steps ≤ 192*W := by
    have := Bit.add_steps xs ys
    dsimp [W] at *
    omega
  have hl (x y : Word) (hx : x.length ≤ a.size) (hy : y.length ≤ b.size) :
      (Bit.mul x y).value.length ≤ W := by
    have := Bit.mul_length x y
    dsimp [W]
    omega
  have a₀ : a.plus.length ≤ a.size := le_max_left _ _
  have a₁ : a.minus.length ≤ a.size := le_max_right _ _
  have b₀ : b.plus.length ≤ b.size := le_max_left _ _
  have b₁ : b.minus.length ≤ b.size := le_max_right _ _
  have h₀ := h _ _ a₀ b₀
  have h₁ := h _ _ a₁ b₁
  have h₂ := h _ _ a₀ b₁
  have h₃ := h _ _ a₁ b₀
  have hp := ha _ _ (hl _ _ a₀ b₀) (hl _ _ a₁ b₁)
  have hn := ha _ _ (hl _ _ a₀ b₁) (hl _ _ a₁ b₀)
  have hW : 1 ≤ W := by dsimp [W]; omega
  have hw : W ≤ W*W := by nlinarith
  change 24 + _ + _ + _ + _ + _ + _ ≤ 4096*W^2
  nlinarith

def isZero (a : Signed) : Run Bool := equal a.plus a.minus

theorem isZero_spec (a : Signed) : a.isZero.value = true ↔ a.number = 0 := by
  rw [isZero, equal_spec, number, sub_eq_zero]
  exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩

theorem isZero_steps (a : Signed) : a.isZero.steps ≤ 64*(a.size+1) := by
  have h := equal_steps a.plus a.minus
  have hp : a.plus.length ≤ a.size := le_max_left _ _
  have hn : a.minus.length ≤ a.size := le_max_right _ _
  exact h.trans (by omega)

def ofBool (b : Bool) : Signed := ⟨if b then [true] else [], []⟩

@[simp] theorem ofBool_number (b : Bool) : (ofBool b).number = (if b then 1 else 0) := by
  cases b <;> rfl

theorem ofBool_size (b : Bool) : (ofBool b).size ≤ 1 := by cases b <;> decide

end Signed

/-- An exact rational is stored as an unreduced numerator and nonzero
denominator. The bit algorithm never normalizes by a gcd. -/
structure Fraction where
  num : Signed
  den : Signed

namespace Fraction

def valid (a : Fraction) : Prop := a.den.number ≠ 0
def size (a : Fraction) : ℕ := max a.num.size a.den.size
def rat (a : Fraction) : ℚ := (a.num.number : ℚ) / a.den.number

def ofBool (b : Bool) : Fraction := ⟨Signed.ofBool b, Signed.ofBool true⟩

@[simp] theorem ofBool_rat (b : Bool) : (ofBool b).rat = (if b then 1 else 0) := by
  cases b <;> norm_num [ofBool, rat]

theorem ofBool_size (b : Bool) : (ofBool b).size ≤ 1 :=
  max_le (Signed.ofBool_size b) (Signed.ofBool_size true)

theorem ofBool_valid (b : Bool) : (ofBool b).valid := by
  simp [ofBool, valid]

def add (a b : Fraction) : Run Fraction :=
  let x := Signed.mul a.num b.den
  let y := Signed.mul b.num a.den
  let n := Signed.add x.value y.value
  let d := Signed.mul a.den b.den
  ⟨⟨n.value,d.value⟩, 16+x.steps+y.steps+n.steps+d.steps⟩

def mul (a b : Fraction) : Run Fraction :=
  let n := Signed.mul a.num b.num
  let d := Signed.mul a.den b.den
  ⟨⟨n.value,d.value⟩, 8+n.steps+d.steps⟩

def neg (a : Fraction) : Run Fraction := ⟨⟨a.num.neg,a.den⟩, 8⟩

def inv (a : Fraction) : Run Fraction :=
  let r := a.num.isZero
  ⟨if r.value then ofBool false else ⟨a.den,a.num⟩, 16+r.steps⟩

theorem add_valid {a b : Fraction} (ha : a.valid) (hb : b.valid) : (add a b).value.valid := by
  simpa only [add, valid, Signed.mul_number] using mul_ne_zero ha hb
theorem mul_valid {a b : Fraction} (ha : a.valid) (hb : b.valid) : (mul a b).value.valid := by
  simpa only [mul, valid, Signed.mul_number] using mul_ne_zero ha hb
theorem neg_valid {a : Fraction} (ha : a.valid) : (neg a).value.valid := ha
theorem inv_valid (a : Fraction) : (inv a).value.valid := by
  simp only [inv]
  split
  · exact ofBool_valid _
  next h =>
    exact fun hn => h ((Signed.isZero_spec a.num).mpr hn)

theorem add_rat {a b : Fraction} (ha : a.valid) (hb : b.valid) :
    (add a b).value.rat = a.rat+b.rat := by
  have ha' : (a.den.number : ℚ) ≠ 0 := by exact_mod_cast ha
  have hb' : (b.den.number : ℚ) ≠ 0 := by exact_mod_cast hb
  simp only [add, rat, Signed.add_number, Signed.mul_number, Int.cast_mul, Int.cast_add]
  rw [div_add_div _ _ ha' hb']
  ring

theorem mul_rat (a b : Fraction) : (mul a b).value.rat = a.rat*b.rat := by
  simp only [mul, rat, Signed.mul_number, Int.cast_mul, div_mul_div_comm]

theorem neg_rat (a : Fraction) : (neg a).value.rat = -a.rat := by
  simp [neg, rat, neg_div]

theorem inv_rat (a : Fraction) : (inv a).value.rat = a.rat⁻¹ := by
  simp only [inv]
  split
  next h =>
    have he := (Signed.isZero_spec a.num).mp h
    simp [ofBool, rat, he]
  next _ => exact inv_div _ _ |>.symm

theorem num_size (a : Fraction) : a.num.size ≤ a.size := le_max_left _ _
theorem den_size (a : Fraction) : a.den.size ≤ a.size := le_max_right _ _

theorem add_size (a b : Fraction) : (add a b).value.size ≤ a.size+b.size+2 := by
  have h₀ := (Signed.mul_size a.num b.den).trans (by have := num_size a; have := den_size b; omega :
    a.num.size+b.den.size+1 ≤ a.size+b.size+1)
  have h₁ := (Signed.mul_size b.num a.den).trans (by have := num_size b; have := den_size a; omega :
    b.num.size+a.den.size+1 ≤ a.size+b.size+1)
  have hn := (Signed.add_size _ _).trans
    (Nat.add_le_add_right (max_le h₀ h₁) 1)
  have hd := Signed.mul_size a.den b.den
  have ha := den_size a
  have hb := den_size b
  exact max_le hn (hd.trans (by omega))

theorem mul_size (a b : Fraction) : (mul a b).value.size ≤ a.size+b.size+2 := by
  have h₀ := Signed.mul_size a.num b.num
  have h₁ := Signed.mul_size a.den b.den
  have h₂ := num_size a
  have h₃ := num_size b
  have h₄ := den_size a
  have h₅ := den_size b
  exact max_le (h₀.trans (by omega)) (h₁.trans (by omega))

theorem neg_size (a : Fraction) : (neg a).value.size = a.size := by simp [neg, size]
theorem inv_size (a : Fraction) : (inv a).value.size ≤ a.size+1 := by
  simp only [inv]
  split
  · exact (ofBool_size false).trans (by omega)
  · change max a.den.size a.num.size ≤ max a.num.size a.den.size+1
    omega

theorem add_steps (a b : Fraction) : (add a b).steps ≤ 32768*(a.size+b.size+2)^2 := by
  let W := a.size+b.size+2
  have a₀ := num_size a
  have a₁ := den_size a
  have b₀ := num_size b
  have b₁ := den_size b
  have h (x y : Signed) (hh : x.size+y.size+1 ≤ W) :
      (Signed.mul x y).steps ≤ 4096*W^2 := by
    exact (Signed.mul_steps _ _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hh _))
  have h₀ := h a.num b.den (by dsimp [W]; omega)
  have h₁ := h b.num a.den (by dsimp [W]; omega)
  have h₂ := h a.den b.den (by dsimp [W]; omega)
  have hs₀ := Signed.mul_size a.num b.den
  have hs₁ := Signed.mul_size b.num a.den
  have h₃ := Signed.add_steps (Signed.mul a.num b.den).value (Signed.mul b.num a.den).value
  have hW : 2 ≤ W := by dsimp [W]; omega
  change 16 + _ + _ + _ + _ ≤ 32768*W^2
  have h₄ : (Signed.add (Signed.mul a.num b.den).value (Signed.mul b.num a.den).value).steps
      ≤ 288*W := by dsimp [W] at *; omega
  nlinarith

theorem mul_steps (a b : Fraction) : (mul a b).steps ≤ 32768*(a.size+b.size+2)^2 := by
  let W := a.size+b.size+2
  have a₀ := num_size a
  have a₁ := den_size a
  have b₀ := num_size b
  have b₁ := den_size b
  have h (x y : Signed) (hh : x.size+y.size+1 ≤ W) :
      (Signed.mul x y).steps ≤ 4096*W^2 := by
    exact (Signed.mul_steps _ _).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hh _))
  have h₀ := h a.num b.num (by dsimp [W]; omega)
  have h₁ := h a.den b.den (by dsimp [W]; omega)
  have hW : 2 ≤ W := by dsimp [W]; omega
  change 8+_+_ ≤ 32768*W^2
  nlinarith

theorem inv_steps (a : Fraction) : (inv a).steps ≤ 128*(a.size+1) := by
  have h := Signed.isZero_steps a.num
  have hn := num_size a
  change 16 + _ ≤ _
  omega

end Fraction
end AffineCost.Bit
