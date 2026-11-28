import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option warningAsError true

/-! An executable ordered-pivot elimination.  The recursive matrix is the
Bareiss cross-multiplication update, retaining old pivot rows as zeros.
The old pivot is an explicit divisor; no inverse is provided as input. -/
namespace J3R59
open scoped BigOperators

def dot {n : ℕ} (a x : Fin n → ℚ) : ℚ :=
  ∑ j, a j * x j

def join {n : ℕ} (h : ℚ) (x : Fin n → ℚ) : Fin (n+1) → ℚ :=
  Fin.cases h x

def tailMatrix {R : Type*} {n : ℕ}
    (A : R → Fin (n+1) → ℚ) (p : R) (prev : ℚ) :
    R → Fin n → ℚ :=
  fun r j => (A p 0 * A r j.succ - A r 0 * A p j.succ) / prev

def tailRhs {R : Type*} {n : ℕ}
    (A : R → Fin (n+1) → ℚ) (b : R → ℚ) (p : R) (prev : ℚ) : R → ℚ :=
  fun r => (A p 0 * b r - A r 0 * b p) / prev

def backHead {R : Type*} {n : ℕ}
    (A : R → Fin (n+1) → ℚ) (b : R → ℚ) (p : R) (x : Fin n → ℚ) : ℚ :=
  (b p - dot (fun j => A p j.succ) x) / A p 0

/-- The list is an ordered catalogue of rows, not a supplied pivot map. -/
def fractionFree {R : Type*} (rows : List R) :
    (n : ℕ) → (R → Fin n → ℚ) → (R → ℚ) → ℚ → Option (Fin n → ℚ)
  | 0, _, _, _ => some (fun j => Fin.elim0 j)
  | n + 1, A, b, prev =>
    match rows.find? (fun r => decide (A r 0 ≠ 0)) with
    | none => none
    | some p =>
      (fractionFree rows n (tailMatrix A p prev) (tailRhs A b p prev)
        (A p 0)).map (fun x => join (backHead A b p x) x)

theorem dot_join {n : ℕ} (a : Fin (n+1) → ℚ) (h : ℚ) (x : Fin n → ℚ) :
    dot a (join h x) = a 0 * h + dot (fun j => a j.succ) x := by
  rw [dot, Fin.sum_univ_succ]
  rfl

theorem join_self {n : ℕ} (x : Fin (n+1) → ℚ) :
    join (x 0) (fun j => x j.succ) = x := by
  funext i
  refine Fin.cases ?_ (fun _ => ?_) i <;> rfl

theorem tail_dot {R : Type*} {n : ℕ} (A : R → Fin (n+1) → ℚ)
    (p r : R) (prev : ℚ) (x : Fin n → ℚ) :
    dot (tailMatrix A p prev r) x =
      (A p 0 * dot (fun j => A r j.succ) x -
        A r 0 * dot (fun j => A p j.succ) x) / prev := by
  unfold dot
  simp only [tailMatrix, div_eq_mul_inv, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem tail_exact {R : Type*} {n : ℕ} (A : R → Fin (n+1) → ℚ) (b : R → ℚ)
    (p : R) (prev : ℚ) (x : Fin (n+1) → ℚ) (hx : ∀ r, dot (A r) x = b r) :
    ∀ r, dot (tailMatrix A p prev r) (fun j => x j.succ) = tailRhs A b p prev r := by
  intro r
  rw [tail_dot, tailRhs]
  apply congrArg (fun y : ℚ => y / prev)
  have hr := hx r
  have hp := hx p
  rw [← join_self x, dot_join] at hr hp
  change A r 0 * x 0 + dot (fun j => A r j.succ) (fun j => x j.succ) = b r at hr
  change A p 0 * x 0 + dot (fun j => A p j.succ) (fun j => x j.succ) = b p at hp
  linear_combination A p 0 * hr - A r 0 * hp

theorem head_exact {R : Type*} {n : ℕ} (A : R → Fin (n+1) → ℚ) (b : R → ℚ)
    (p : R) (x : Fin (n+1) → ℚ) (hx : dot (A p) x = b p) (hp : A p 0 ≠ 0) :
    backHead A b p (fun j => x j.succ) = x 0 := by
  rw [← join_self x, dot_join] at hx
  unfold backHead
  apply (div_eq_iff hp).mpr
  linear_combination -hx

theorem tail_zero_injective {R : Type*} {n : ℕ} (A : R → Fin (n+1) → ℚ)
    (p : R) (prev : ℚ) (hp : A p 0 ≠ 0) (hq : prev ≠ 0)
    (inj : ∀ x : Fin (n+1) → ℚ, (∀ r, dot (A r) x = 0) → x = 0) :
    ∀ x : Fin n → ℚ, (∀ r, dot (tailMatrix A p prev r) x = 0) → x = 0 := by
  intro x hx
  let h := -dot (fun j => A p j.succ) x / A p 0
  have hh : A p 0 * h = -dot (fun j => A p j.succ) x := by
    rw [mul_comm]
    exact ((div_eq_iff hp).mp
      (show -dot (fun j => A p j.succ) x / A p 0 = h from rfl)).symm
  have hz (r : R) : dot (A r) (join h x) = 0 := by
    have ht := hx r
    rw [tail_dot] at ht
    have hn : A p 0 * dot (fun j => A r j.succ) x -
        A r 0 * dot (fun j => A p j.succ) x = 0 := by
      simpa using (div_eq_iff hq).mp ht
    apply (mul_eq_zero.mp (show A p 0 * dot (A r) (join h x) = 0 by
      rw [dot_join]
      linear_combination hn + A r 0 * hh)).resolve_left hp
  have hj := inj (join h x) hz
  funext j
  exact congrFun hj j.succ

/-- Exact for a consistent full-column-rank system: both hypotheses are
semantic statements, and neither supplies numerical auxiliary data. -/
theorem fractionFree_exact {R : Type*} (rows : List R) (allRows : ∀ r, r ∈ rows)
    (n : ℕ) (A : R → Fin n → ℚ) (b : R → ℚ) (prev : ℚ) (hprev : prev ≠ 0)
    (inj : ∀ x : Fin n → ℚ, (∀ r, dot (A r) x = 0) → x = 0)
    (x : Fin n → ℚ) (hx : ∀ r, dot (A r) x = b r) :
    fractionFree rows n A b prev = some x := by
  induction n generalizing b prev with
  | zero =>
    have h : (fun j : Fin 0 => Fin.elim0 (α:=ℚ) j) = x := by
      funext j
      exact j.elim0
    simp only [fractionFree, h]
  | succ n ih =>
    have pivot : ∃ r, A r 0 ≠ 0 := by
      by_contra hall
      have hz (r : R) : A r 0 = 0 := by
        by_contra hnr
        exact hall ⟨r, hnr⟩
      have hc (r : R) : dot (A r) (join 1 (fun _ => 0)) = 0 := by
        rw [dot_join, hz r]
        simp [dot]
      have he := congrFun (inj (join 1 (fun _ => 0)) hc) 0
      change (1 : ℚ) = 0 at he
      exact one_ne_zero he
    cases hf : rows.find? (fun r => decide (A r 0 ≠ 0)) with
    | none =>
      obtain ⟨r,hr⟩ := pivot
      have hbad := (List.find?_eq_none.mp hf) r (allRows r)
      simp [hr] at hbad
    | some p =>
      have hp' : (fun r : R => decide (A r 0 ≠ 0)) p = true :=
        List.find?_some (p := fun r : R => decide (A r 0 ≠ 0)) (a := p) hf
      have hp : A p 0 ≠ 0 := of_decide_eq_true hp'
      rw [fractionFree, hf]
      have hrec : fractionFree rows n (tailMatrix A p prev) (tailRhs A b p prev)
          (A p 0) = some (fun j => x j.succ) := by
        apply ih
        · exact hp
        · exact tail_zero_injective A p prev hp hprev inj
        · exact tail_exact A b p prev x hx
      change (fractionFree rows n (tailMatrix A p prev) (tailRhs A b p prev) (A p 0)).map
        (fun y => join (backHead A b p y) y) = some x
      rw [hrec]
      simp only [Option.map_some, head_exact A b p x (hx p) hp, join_self]

#print axioms fractionFree_exact
#print axioms tail_zero_injective
#print axioms tail_exact
#print axioms head_exact

end J3R59
