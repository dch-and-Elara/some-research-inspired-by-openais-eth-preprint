import J6Precision
import Mathlib.Tactic

/-! Finite absolute-numerator bound for the full two-assignment
contraction. There is no estimate based on cancellation or rank. -/
namespace J6NativeHeight
open scoped BigOperators
variable {P : Type*} [Fintype P] [DecidableEq P]

def entry (n d : ℤ) (row col : Bool) : ℤ :=
  if row then (if col then n else 0) else d - (if col then n else 0)

theorem entry_abs (n d C : ℤ) (hn : |n| ≤ C) (hd : |d| ≤ C)
    (row col : Bool) : |entry n d row col| ≤ 2*C := by
  have hC : 0 ≤ C := (abs_nonneg n).trans hn
  have h : |d-n| ≤ |d|+|n| := abs_sub _ _
  cases row <;> cases col <;> simp [entry] <;> linarith

def numerator (A B : (P → Bool) → Bool) (read : P → (P → Bool) → Bool)
    (n d : ℤ) : ℤ :=
  ∑ y : P → Bool, ∑ x : P → Bool,
    if A y && B x then ∏ p, entry n d (y p) (read p x) else 0

theorem numerator_abs (A B : (P → Bool) → Bool) (read : P → (P → Bool) → Bool)
    (n d C : ℤ) (hn : |n| ≤ C) (hd : |d| ≤ C) :
    |numerator A B read n d| ≤
      (2:ℤ)^(2*Fintype.card P) * (2*C)^Fintype.card P := by
  let r := Fintype.card P
  let b := (2*C)^r
  have hb : 0 ≤ b := pow_nonneg (by linarith [abs_nonneg n]) _
  have hterm (y x : P → Bool) :
      |if A y && B x then ∏ p, entry n d (y p) (read p x) else 0| ≤ b := by
    split
    · rw [Finset.abs_prod]
      have hp := Finset.prod_le_prod (s := (Finset.univ : Finset P))
        (f := fun p => |entry n d (y p) (read p x)|) (g := fun _ => 2*C)
        (fun _ _ => abs_nonneg _) (fun p _ => entry_abs n d C hn hd (y p) (read p x))
      simpa [b,r] using hp
    · simpa using hb
  let f (y x : P → Bool) : ℤ := if A y && B x then
    ∏ p, entry n d (y p) (read p x) else 0
  have he (y : P → Bool) : |∑ x, f y x| ≤ (2:ℤ)^r*b := by
    calc
      _ ≤ ∑ x, |f y x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _x : P → Bool, b := Finset.sum_le_sum fun x _ => hterm y x
      _ = _ := by simp [r]
  change |∑ y, ∑ x, f y x| ≤ _
  calc
    _ ≤ ∑ y, |∑ x, f y x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _y : P → Bool, (2:ℤ)^r*b := Finset.sum_le_sum fun y _ => he y
    _ = (2:ℤ)^r*((2:ℤ)^r*b) := by simp [r]
    _ = _ := by
      rw [← mul_assoc,← pow_add]
      unfold b r
      congr 2
      omega

/-- The exact source-sized bound used by the precision lemma. It applies to
any row/column Boolean tensors and any registered predecessor/default-zero read. -/
theorem physical_height (m t : ℕ) (hP : Fintype.card P = J6Mesh.M m)
    (A B : (P → Bool) → Bool) (read : P → (P → Bool) → Bool) (n d : ℤ)
    (hn : |n| ≤ (2:ℤ)^(t*(J6Mesh.a m+1)))
    (hd : |d| ≤ (2:ℤ)^(t*(J6Mesh.a m+1))) :
    |numerator A B read n d| ≤ (↑((2:ℕ)^(J6Precision.height m t)):ℤ) := by
  have h := numerator_abs A B read n d _ hn hd
  rw [hP] at h
  push_cast
  refine h.trans_eq ?_
  rw [← pow_succ',← pow_mul,← pow_add]
  unfold J6Precision.height
  congr 1
  ring

#print axioms numerator_abs
#print axioms physical_height
end J6NativeHeight
