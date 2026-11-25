import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Basic
import Lean.Elab.Tactic.Omega

open scoped BigOperators

namespace AffineEdge

abbrev Bits (q : ℕ) := Fin q → Bool

def flip {q : ℕ} (t : Fin q) (a : Bits q) : Bits q :=
  fun j => if j = t then !(a j) else a j

@[simp] theorem flip_same {q : ℕ} (t : Fin q) (a : Bits q) :
    flip t a t = !(a t) := by simp [flip]

@[simp] theorem flip_other {q : ℕ} {t j : Fin q} (h : j ≠ t) (a : Bits q) :
    flip t a j = a j := by simp [flip, h]

@[simp] theorem flip_flip {q : ℕ} (t : Fin q) (a : Bits q) :
    flip t (flip t a) = a := by
  funext j
  by_cases h : j = t
  · subst j
    simp
  · simp [h]

def flipEquiv {q : ℕ} (t : Fin q) : Bits q ≃ Bits q where
  toFun := flip t
  invFun := flip t
  left_inv := flip_flip t
  right_inv := flip_flip t

/-- If every cube edge has an exceptional endpoint and each vertex is
exceptional in at most `k` directions, then `q ≤ 2*k`. -/
theorem edge_count {q k : ℕ} (bad : Bits q → Fin q → Prop)
    [∀ a t, Decidable (bad a t)]
    (hEdge : ∀ a t, bad a t ∨ bad (flip t a) t)
    (hVertex : ∀ a, (Finset.univ.filter (bad a)).card ≤ k) :
    q ≤ 2*k := by
  let f (a : Bits q) (t : Fin q) : ℕ := if bad a t then 1 else 0
  let N := Fintype.card (Bits q)
  have ht (t : Fin q) : N ≤ 2 * (∑ a : Bits q, f a t) := by
    have he : (∑ a : Bits q, f (flip t a) t) = ∑ a : Bits q, f a t :=
      (flipEquiv t).sum_comp (fun a => f a t)
    calc
      N = ∑ _ : Bits q, (1 : ℕ) := by simp [N]
      _ ≤ ∑ a : Bits q, (f a t + f (flip t a) t) := by
        apply Finset.sum_le_sum
        intro a _
        rcases hEdge a t with h | h <;> simp [f, h]
      _ = _ := by rw [Finset.sum_add_distrib, he, two_mul]
  have hv (a : Bits q) : (∑ t, f a t) ≤ k := by
    simpa only [f, Finset.sum_boole, Nat.cast_id] using hVertex a
  have bound : q * N ≤ (2*k) * N := by
    calc
      _ = ∑ _ : Fin q, N := by simp
      _ ≤ ∑ t : Fin q, 2 * (∑ a : Bits q, f a t) :=
        Finset.sum_le_sum fun t _ => ht t
      _ = 2 * (∑ a : Bits q, ∑ t : Fin q, f a t) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ 2 * (∑ _ : Bits q, k) :=
        Nat.mul_le_mul_left _ (Finset.sum_le_sum fun a _ => hv a)
      _ = _ := by simp [N, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  have hN : 0 < N := Fintype.card_pos_iff.mpr ⟨fun _ => false⟩
  exact Nat.le_of_mul_le_mul_right bound hN

end AffineEdge
