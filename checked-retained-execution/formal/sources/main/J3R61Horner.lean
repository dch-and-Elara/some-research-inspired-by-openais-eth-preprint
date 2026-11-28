import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2900000

/-! Actual two-scalar Horner and product loops. Each step returns its
arithmetic counter along with its computed data. -/
namespace J3R61
open Polynomial

structure Pair (α : Type*) where
  c : α
  d : α
  deriving DecidableEq

@[ext] theorem Pair.ext' {α : Type*} {a b : Pair α} (hc : a.c=b.c) (hd : a.d=b.d) : a=b := by
  cases a; cases b; cases hc; cases hd; rfl

def Pair.scalar {α : Type*} [Zero α] (a : α) : Pair α := ⟨a,0⟩
def Pair.plus {α : Type*} [Add α] (a b : Pair α) : Pair α := ⟨a.c+b.c,a.d+b.d⟩
def Pair.minus {α : Type*} [Sub α] (a b : Pair α) : Pair α := ⟨a.c-b.c,a.d-b.d⟩
def Pair.times {α : Type*} [Add α] [Mul α] (a b : Pair α) : Pair α :=
  ⟨a.c*b.c,a.c*b.d+a.d*b.c⟩

def capture {α : Type*} [Semiring α] (p : α[X]) : Pair α := ⟨p.coeff 0,p.coeff 1⟩

@[simp] theorem capture_one {α : Type*} [Semiring α] : capture (1:α[X]) = Pair.scalar 1 := by
  ext <;> simp [capture,Pair.scalar,coeff_one]

@[simp] theorem capture_scalar {α : Type*} [Semiring α] (a : α) :
    capture (C a) = Pair.scalar a := by
  ext <;> simp [capture,Pair.scalar]

@[simp] theorem capture_sub {α : Type*} [Ring α] (p q : α[X]) :
    capture (p-q) = (capture p).minus (capture q) := by
  ext <;> simp [capture,Pair.minus]

@[simp] theorem capture_mul {α : Type*} [Semiring α] (p q : α[X]) :
    capture (p*q) = (capture p).times (capture q) := by
  ext <;> simp [capture,Pair.times,mul_coeff_zero,mul_coeff_one,add_comm]

structure Paid (α : Type*) where
  value : α
  ops : ℕ

def Pair.intSize (x : Pair ℤ) : ℕ := x.c.natAbs+x.d.natAbs

def hornerStep (t a : ℤ) (p : Pair ℤ) : Pair ℤ := ⟨a+t*p.c,p.c+t*p.d⟩

def horner (t : ℤ) : List ℤ → Paid (Pair ℤ)
  | [] => ⟨Pair.scalar 0,0⟩
  | a :: as =>
    let z := horner t as
    ⟨hornerStep t a z.value, z.ops+4⟩

noncomputable def tapePoly : List ℤ → ℤ[X]
  | [] => 0
  | a :: as => C a + X * tapePoly as

theorem tapePoly_coeff (ls : List ℤ) (k : ℕ) : (tapePoly ls).coeff k = ls[k]?.getD 0 := by
  induction ls generalizing k with
  | nil => simp [tapePoly]
  | cons x xs ih =>
    cases k with
    | zero => simp [tapePoly]
    | succ k =>
      change (C x + X*tapePoly xs).coeff (k+1) = _
      rw [coeff_add,coeff_C_succ,zero_add,coeff_X_mul,ih]
      rfl

theorem horner_actual_coeffs (t : ℤ) (ls : List ℤ) :
    (horner t ls).value = ⟨(tapePoly ls).eval t,(tapePoly ls).derivative.eval t⟩ := by
  induction ls with
  | nil => simp [horner,tapePoly,Pair.scalar]
  | cons x xs ih =>
    change hornerStep t x (horner t xs).value = _
    rw [ih]
    ext <;> simp [hornerStep,tapePoly,derivative_mul]

theorem horner_actual_ops (t : ℤ) (ls : List ℤ) :
    (horner t ls).ops = 4*ls.length := by
  induction ls with
  | nil => rfl
  | cons x xs ih =>
    simp only [horner,List.length_cons,ih,Nat.mul_succ]

theorem horner_step_size (t a : ℤ) (p : Pair ℤ) (Q B : ℕ)
    (ht : t.natAbs ≤ Q) (ha : a.natAbs ≤ B) :
    (hornerStep t a p).intSize ≤ B+(Q+1)*p.intSize := by
  unfold hornerStep Pair.intSize
  have h1 : (a+t*p.c).natAbs ≤ B+Q*p.c.natAbs :=
    (Int.natAbs_add_le a (t*p.c)).trans (Nat.add_le_add ha
      (by simpa only [Int.natAbs_mul] using Nat.mul_le_mul_right p.c.natAbs ht))
  have h2 : (p.c+t*p.d).natAbs ≤ p.c.natAbs+Q*p.d.natAbs :=
    (Int.natAbs_add_le p.c (t*p.d)).trans (Nat.add_le_add_left
      (by simpa only [Int.natAbs_mul] using Nat.mul_le_mul_right p.d.natAbs ht) _)
  apply (Nat.add_le_add h1 h2).trans
  rw [show (Q+1)*(p.c.natAbs+p.d.natAbs) =
    Q*p.c.natAbs+(p.c.natAbs+Q*p.d.natAbs)+p.d.natAbs by ring]
  omega

def hornerCap (Q B k : ℕ) := k*B*(Q+1)^k

theorem horner_actual_size (t : ℤ) (ls : List ℤ) (Q B : ℕ)
    (ht : t.natAbs ≤ Q) (hb : ∀ x ∈ ls, x.natAbs ≤ B) :
    (horner t ls).value.intSize ≤ hornerCap Q B ls.length := by
  induction ls with
  | nil => simp [horner,hornerCap,Pair.scalar,Pair.intSize]
  | cons x xs ih =>
    have h := horner_step_size t x (horner t xs).value Q B ht
      (hb x (List.mem_cons_self ..))
    have hi := ih (fun a hm => hb a (List.mem_cons_of_mem _ hm))
    change (hornerStep t x (horner t xs).value).intSize ≤ _
    apply h.trans
    apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ hi) _).trans
    have hn : (1:ℕ) ≤ (Q+1)^(xs.length+1) :=
      Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega))
    calc
      _ ≤ B*(Q+1)^(xs.length+1) + (Q+1)*hornerCap Q B xs.length := by
        exact Nat.add_le_add_right (by simpa only [mul_one] using Nat.mul_le_mul_left B hn) _
      _ = _ := by
        simp only [hornerCap,List.length_cons,pow_succ]
        ring

theorem hornerCap_mono (Q B : ℕ) {k l : ℕ} (hk : k ≤ l) :
    hornerCap Q B k ≤ hornerCap Q B l := by
  exact Nat.mul_le_mul (Nat.mul_le_mul_right _ hk) (Nat.pow_le_pow_right (by omega) hk)

/-- Every recursive state is the same Horner computation on a suffix,
so the cap applies inside the actual computation as well as at output. -/
theorem horner_actual_suffix_width (t : ℤ) (ls : List ℤ) (Q B R : ℕ)
    (ht : t.natAbs ≤ Q) (hb : ∀ x ∈ ls, x.natAbs ≤ B) (hr : ls.length ≤ R)
    (k : ℕ) :
    (horner t (ls.drop k)).value.intSize ≤ hornerCap Q B R := by
  apply (horner_actual_size t (ls.drop k) Q B ht
    (fun a hm => hb a (List.mem_of_mem_drop hm))).trans
  apply hornerCap_mono
  rw [List.length_drop]
  omega

def product : List (Pair ℤ) → Paid (Pair ℤ)
  | [] => ⟨Pair.scalar 1,0⟩
  | x :: xs =>
    let p := product xs
    ⟨x.times p.value,p.ops+4⟩

theorem product_actual_ops (ls : List (Pair ℤ)) : (product ls).ops = 4*ls.length := by
  induction ls with
  | nil => rfl
  | cons x xs ih =>
    simp only [product,ih,List.length_cons,Nat.mul_succ]

theorem product_actual_coeffs (ls : List ℤ[X]) :
    (product (ls.map capture)).value = capture ls.prod := by
  induction ls with
  | nil => simp [product]
  | cons x xs ih => simp only [List.map_cons, List.prod_cons, product, ih, capture_mul]

theorem pair_product_size (a b : Pair ℤ) : (a.times b).intSize ≤ a.intSize*b.intSize := by
  unfold Pair.times Pair.intSize
  have h := Int.natAbs_add_le (a.c*b.d) (a.d*b.c)
  have hd : 0 ≤ a.d.natAbs*b.d.natAbs := Nat.zero_le _
  simp only [Int.natAbs_mul,Nat.add_mul,Nat.mul_add] at *
  omega

theorem product_actual_size (ls : List (Pair ℤ)) :
    (product ls).value.intSize ≤ (ls.map Pair.intSize).prod := by
  induction ls with
  | nil => simp [product,Pair.scalar,Pair.intSize]
  | cons x xs ih =>
    rw [product,List.map_cons,List.prod_cons]
    exact (pair_product_size _ _).trans (Nat.mul_le_mul_left _ ih)

#print axioms tapePoly_coeff
#print axioms horner_actual_coeffs
#print axioms horner_actual_ops
#print axioms horner_actual_suffix_width
#print axioms product_actual_coeffs
#print axioms product_actual_ops
#print axioms product_actual_size

end J3R61
