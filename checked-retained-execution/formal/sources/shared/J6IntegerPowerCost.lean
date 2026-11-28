import J6IntegerRoot
import V9BitCost
import Mathlib.Tactic

/-! Arithmetic part of the integer root decoder. The tariff is a declared
repeated-multiplication schoolbook model, not a cost theorem for Lean's
machine interface or for constructing the physical formula. -/
namespace J6IntegerPowerCost

def countedPower (x : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1,0)
  | i+1 => let z := countedPower x i; (z.1*x,z.2+1)

theorem countedPower_spec (x i : ℕ) : countedPower x i = (x^i,i) := by
  induction i with
  | zero => rfl
  | succ i hi => simp [countedPower,hi,pow_succ]

theorem power_width (p x : ℕ) (hx : x < 2^p) (i : ℕ) :
    x^i < 2^(1+i*p) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, Nat.succ_mul, ← Nat.add_assoc, pow_add]
    exact (Nat.mul_le_mul_right x ih.le).trans_lt (Nat.mul_lt_mul_of_pos_left hx (by positivity))

/-- Uniform bound on every intermediate operand of an e-step power. -/
theorem power_width_uniform (p x e i : ℕ) (hx : x < 2^p) (hi : i ≤ e) :
    (countedPower x i).1 < 2^(1+e*p) := by
  rw [countedPower_spec]
  exact (power_width p x hx i).trans_le (Nat.pow_le_pow_right (by decide) (by gcongr))

theorem recovery_power (x e b : ℕ) :
    J6IntegerRoot.recoverNat (fun y => (countedPower y e).1) x b 0 =
      J6IntegerRoot.recoverNat (fun y => y^e) x b 0 := by
  simp only [countedPower_spec]

/-- Width tariff for b successive threshold comparisons. A schoolbook
multiplication is charged 8W², and the final comparison 4W. -/
def charge (b e : ℕ) : ℕ :=
  let w := 1+(e+1)*b
  b*(8*e*w^2+4*w)

theorem charge_poly (b e : ℕ) :
    charge b e ≤ 12*(b+1)^3*(e+1)^3 := by
  let w := 1+(e+1)*b
  have hw : w ≤ (e+1)*(b+1) := by dsimp [w]; nlinarith
  have hww : w^2 ≤ ((e+1)*(b+1))^2 := by gcongr
  have hprod : 8*e*w^2 ≤ 8*(e+1)*((e+1)*(b+1))^2 := by gcongr; omega
  have hp : w ≤ ((e+1)*(b+1))^2*(e+1) := by
    have hpos : 0 < (e+1)*(b+1) := by positivity
    have hl := Nat.le_mul_of_pos_right ((e+1)*(b+1)) hpos
    have hm := Nat.le_mul_of_pos_right (((e+1)*(b+1))^2) (Nat.succ_pos e)
    exact hw.trans ((by simpa [pow_two] using hl : (e+1)*(b+1) ≤ ((e+1)*(b+1))^2).trans hm)
  calc
    charge b e ≤ (b+1)*(8*(e+1)*((e+1)*(b+1))^2+4*(((e+1)*(b+1))^2*(e+1))) :=
      Nat.mul_le_mul (Nat.le_succ _) (Nat.add_le_add hprod (Nat.mul_le_mul_left _ hp))
    _ = _ := by ring

#print axioms countedPower_spec
#print axioms power_width
#print axioms power_width_uniform
#print axioms recovery_power
#print axioms charge_poly
end J6IntegerPowerCost