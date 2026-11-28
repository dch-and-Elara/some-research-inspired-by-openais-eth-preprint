import AffineCostFraction
import AffineCostExpr

namespace AffineCost
open Bit

/-- Sequential indexing of the encoded label list. -/
def labelAt : List Fraction → ℕ → Run Fraction
  | [], _ => ⟨Fraction.ofBool false, 8⟩
  | a :: _, 0 => ⟨a, 8⟩
  | _ :: as, n+1 =>
    let r := labelAt as n
    ⟨r.value, 8+r.steps⟩

theorem labelAt_value (as : List Fraction) (n : ℕ) :
    (labelAt as n).value = (as[n]?).getD (Fraction.ofBool false) := by
  induction as generalizing n with
  | nil => simp [labelAt]
  | cons a as ih => cases n <;> simp [labelAt, ih]

theorem labelAt_steps (as : List Fraction) (n : ℕ) :
    (labelAt as n).steps ≤ 8*(n+1) := by
  induction as generalizing n with
  | nil => simp [labelAt]
  | cons a as ih =>
    cases n with
    | zero => simp [labelAt]
    | succ n => have := ih n; simp only [labelAt]; omega

theorem labelAt_valid (as : List Fraction) (h : ∀ a ∈ as, a.valid) (n : ℕ) :
    (labelAt as n).value.valid := by
  induction as generalizing n with
  | nil => exact Fraction.ofBool_valid _
  | cons a as ih =>
    cases n with
    | zero => exact h a (by simp)
    | succ n => exact ih (fun b hb => h _ (by simp [hb])) _

theorem labelAt_size (as : List Fraction) (L : ℕ) (h : ∀ a ∈ as, a.size ≤ L) (n : ℕ) :
    (labelAt as n).value.size ≤ L+1 := by
  induction as generalizing n with
  | nil => exact (Fraction.ofBool_size _).trans (by omega)
  | cons a as ih =>
    cases n with
    | zero => exact (h a (by simp)).trans (by omega)
    | succ n => exact ih (fun b hb => h _ (by simp [hb])) _

def bitSites (as : List Fraction) (t : Fin q) : ℚ := (labelAt as t.val).value.rat

namespace Expr
variable {q : ℕ}

/-- Execute arithmetic expressions on encoded fractions. The counter measures
the bit primitives used by the executor, rather than charging field operations. -/
def execute (as : List Fraction) : Expr q → Run Fraction
  | .bit b => ⟨Fraction.ofBool b, 8⟩
  | .site t => labelAt as t.val
  | .neg x =>
    let a := x.execute as
    let z := Fraction.neg a.value
    ⟨z.value, 8+a.steps+z.steps⟩
  | .inv x =>
    let a := x.execute as
    let z := Fraction.inv a.value
    ⟨z.value, 8+a.steps+z.steps⟩
  | .add x y =>
    let a := x.execute as
    let b := y.execute as
    let z := Fraction.add a.value b.value
    ⟨z.value, 8+a.steps+b.steps+z.steps⟩
  | .mul x y =>
    let a := x.execute as
    let b := y.execute as
    let z := Fraction.mul a.value b.value
    ⟨z.value, 8+a.steps+b.steps+z.steps⟩

theorem execute_valid (as : List Fraction) (hv : ∀ a ∈ as, a.valid) (x : Expr q) :
    (x.execute as).value.valid := by
  induction x with
  | bit b => exact Fraction.ofBool_valid _
  | site t => exact labelAt_valid _ hv _
  | neg x ih => exact Fraction.neg_valid ih
  | inv x _ => exact Fraction.inv_valid _
  | add x y hx hy => exact Fraction.add_valid hx hy
  | mul x y hx hy => exact Fraction.mul_valid hx hy

theorem execute_rat (as : List Fraction) (hv : ∀ a ∈ as, a.valid) (x : Expr q) :
    (x.execute as).value.rat = x.eval (bitSites as) := by
  induction x with
  | bit b => exact Fraction.ofBool_rat _
  | site t => rfl
  | neg x ih => simp only [execute, eval, Fraction.neg_rat, ih]
  | inv x ih => simp only [execute, eval, Fraction.inv_rat, ih]
  | add x y hx hy =>
    simp only [execute, eval, Fraction.add_rat (execute_valid as hv x) (execute_valid as hv y), hx, hy]
  | mul x y hx hy => simp only [execute, eval, Fraction.mul_rat, hx, hy]

theorem execute_size (as : List Fraction) (L : ℕ) (h : ∀ a ∈ as, a.size ≤ L) (x : Expr q) :
    (x.execute as).value.size ≤ (L+3)*x.nodes := by
  induction x with
  | bit b => exact (Fraction.ofBool_size _).trans (by simp [nodes])
  | site t => exact (labelAt_size _ L h _).trans (by simp [nodes])
  | neg x ih =>
    simp only [execute, Fraction.neg_size, nodes, Nat.mul_add, Nat.mul_one]
    omega
  | inv x ih =>
    simp only [execute, nodes, Nat.mul_add, Nat.mul_one]
    have := Fraction.inv_size (x.execute as).value
    omega
  | add x y hx hy =>
    simp only [execute, nodes, Nat.mul_add, Nat.mul_one]
    have := Fraction.add_size (x.execute as).value (y.execute as).value
    omega
  | mul x y hx hy =>
    simp only [execute, nodes, Nat.mul_add, Nat.mul_one]
    have := Fraction.mul_size (x.execute as).value (y.execute as).value
    omega

def budget (q U : ℕ) : ℕ := 32768*(2*U+2)^2+256*(q+U+2)

theorem execute_steps_aux (as : List Fraction) (L : ℕ) (h : ∀ a ∈ as, a.size ≤ L)
    (x : Expr q) (U : ℕ) (hU : (L+3)*x.nodes ≤ U) :
    (x.execute as).steps ≤ x.nodes * budget q U := by
  have hb : 256*(q+U+2) ≤ budget q U := Nat.le_add_left _ _
  induction x with
  | bit b => simp only [nodes, execute, one_mul]; omega
  | site t =>
    have hh := labelAt_steps as t.val
    have ht := t.isLt
    simp only [nodes, execute, one_mul]
    omega
  | neg x ih =>
    have hc : (L+3)*x.nodes ≤ U := by simp only [nodes, Nat.mul_add, Nat.mul_one] at hU; omega
    simp only [execute, Fraction.neg, nodes, Nat.add_mul, one_mul]
    have := ih hc
    omega
  | inv x ih =>
    have hc : (L+3)*x.nodes ≤ U := by simp only [nodes, Nat.mul_add, Nat.mul_one] at hU; omega
    have hw := (execute_size as L h x).trans hc
    have hi := Fraction.inv_steps (x.execute as).value
    simp only [execute, nodes, Nat.add_mul, one_mul]
    have := ih hc
    omega
  | add x y hx hy =>
    have hc : (L+3)*x.nodes ≤ U := by simp only [nodes, Nat.mul_add, Nat.mul_one] at hU; omega
    have hd : (L+3)*y.nodes ≤ U := by simp only [nodes, Nat.mul_add, Nat.mul_one] at hU; omega
    have ha := (execute_size as L h x).trans hc
    have hb' := (execute_size as L h y).trans hd
    have ee : (x.execute as).value.size+(y.execute as).value.size+2 ≤ 2*U+2 := by omega
    have ht := (Fraction.add_steps (x.execute as).value (y.execute as).value).trans
      (Nat.mul_le_mul_left 32768 (Nat.pow_le_pow_left ee 2))
    have he := hx hc
    have hf := hy hd
    have hg : 8+((x.execute as).value.add (y.execute as).value).steps ≤ budget q U := by
      unfold budget
      omega
    simp only [execute, nodes, Nat.add_mul, one_mul]
    omega
  | mul x y hx hy =>
    have hc : (L+3)*x.nodes ≤ U := by simp only [nodes, Nat.mul_add, Nat.mul_one] at hU; omega
    have hd : (L+3)*y.nodes ≤ U := by simp only [nodes, Nat.mul_add, Nat.mul_one] at hU; omega
    have ha := (execute_size as L h x).trans hc
    have hb' := (execute_size as L h y).trans hd
    have ee : (x.execute as).value.size+(y.execute as).value.size+2 ≤ 2*U+2 := by omega
    have ht := (Fraction.mul_steps (x.execute as).value (y.execute as).value).trans
      (Nat.mul_le_mul_left 32768 (Nat.pow_le_pow_left ee 2))
    have he := hx hc
    have hf := hy hd
    have hg : 8+((x.execute as).value.mul (y.execute as).value).steps ≤ budget q U := by
      unfold budget
      omega
    simp only [execute, nodes, Nat.add_mul, one_mul]
    omega

theorem execute_steps (as : List Fraction) (L : ℕ) (h : ∀ a ∈ as, a.size ≤ L)
    (x : Expr q) (N : ℕ) (hN : x.nodes ≤ N) :
    (x.execute as).steps ≤ N * budget q ((L+3)*N) :=
  (execute_steps_aux as L h x _ (Nat.mul_le_mul_left _ hN)).trans (Nat.mul_le_mul_right _ hN)

end Expr
end AffineCost
