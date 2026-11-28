
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace NativeBitBudget
open scoped BigOperators
variable {A P T : Type*} [Fintype A] [Fintype P] [Fintype T]

def tileMoment (u : T → ℕ) (bit : T → Bool) (b : ℕ) : ℕ :=
  ∑ t, u t ^ b * (if bit t then 1 else 0)

theorem tileMoment_le (u : T → ℕ) (bit : T → Bool) (b L : ℕ)
    (hT : Fintype.card T ≤ L) (hcoord : ∀ t, u t ≤ L) :
    tileMoment u bit b ≤ L ^ (b+1) := by
  unfold tileMoment
  calc
    _ ≤ ∑ _t : T, L ^ b := by
      apply Finset.sum_le_sum
      intro t _
      have h := Nat.pow_le_pow_left (hcoord t) b
      cases bit t <;> simp_all
    _ = Fintype.card T * L ^ b := by simp
    _ ≤ L * L ^ b := Nat.mul_le_mul_right _ hT
    _ = L ^ (b+1) := by rw [pow_succ, Nat.mul_comm]

/-- Integer weights once zero-probe rows are reduced to unary factors. -/
def weight (table : A → ℕ) (hit : A → P → Bool) (absoluteKernel : ℕ) (x : A) : ℕ :=
  table x * ∏ p, (1 + if hit x p then absoluteKernel else 0)

omit [Fintype A] in
theorem weight_le (table : A → ℕ) (hit : A → P → Bool) (C : ℕ)
    (hTable : ∀ a, table a ≤ 1) (x : A) :
    weight table hit C x ≤ (1 + C) ^ Fintype.card P := by
  unfold weight
  have h := Finset.prod_le_prod' (s := (Finset.univ : Finset P))
    (f := fun p => 1 + if hit x p then C else 0) (g := fun _ => 1+C)
    (fun p _ => by
      change 1 + (if hit x p then C else 0) ≤ 1+C
      cases hit x p <;> simp)
  simpa using Nat.mul_le_mul (hTable x) h

/-- J7 acquisition-width bound, given the certified port count. The extra
    budget accounts for powers of the tile coordinates. -/
theorem moment_sum_bound (table : A → ℕ) (hit : A → P → Bool)
    (coord : T → ℕ) (bit : A → T → Bool) (C M L b extra : ℕ)
    (hTable : ∀ a, table a ≤ 1)
    (hA : Fintype.card A ≤ 2 ^ M) (hP : Fintype.card P * L ≤ 3 * M)
    (hT : Fintype.card T ≤ L) (hcoord : ∀ t, coord t ≤ L)
    (hKernel : 1+C ≤ 2 ^ (2 * L)) (hExtra : L ^ (b+1) ≤ 2 ^ extra) :
    (∑ a : A, weight table hit C a * tileMoment coord (bit a) b) ≤
      2 ^ (7 * M + extra) := by
  let k := Fintype.card P
  have h1 : (1+C)^k ≤ 2 ^ (6*M) := by
    calc
      _ ≤ (2 ^ (2 * L)) ^ k := Nat.pow_le_pow_left hKernel _
      _ = 2 ^ ((2 * L) * k) := (pow_mul (2 : ℕ) (2*L) k).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by dsimp [k]; nlinarith)
  calc
    _ ≤ ∑ _a : A, 2 ^ (6*M) * 2 ^ extra :=
      Finset.sum_le_sum fun a _ => Nat.mul_le_mul
        ((weight_le table hit C hTable a).trans h1)
        ((tileMoment_le coord (bit a) b L hT hcoord).trans hExtra)
    _ ≤ 2 ^ M * (2 ^ (6*M) * 2 ^ extra) := by
      simpa using Nat.mul_le_mul_right (2 ^ (6*M) * 2 ^ extra) hA
    _ = _ := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega

#print axioms tileMoment_le
#print axioms weight_le
#print axioms moment_sum_bound
end NativeBitBudget

