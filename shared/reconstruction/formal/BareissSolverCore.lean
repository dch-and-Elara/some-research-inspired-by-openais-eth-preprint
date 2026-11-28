import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Deterministic elimination on rectangular rational systems

Pivot selection is row-major. Each nonzero pivot reduces both dimensions.
Free coordinates are assigned zero, and a nonzero residual right-hand side
in a zero coefficient system gives `none`. The dense tables store arithmetic
results before the next recursive call.
-/

open scoped BigOperators

namespace Reconstruction.BareissSolver

abbrev Coefficients (m n : ℕ) := Matrix (Fin m) (Fin n) ℚ
abbrev Column (n : ℕ) := Fin n → ℚ

def denseColumn {n : ℕ} (f : Column n) : Column n :=
  let values := Vector.ofFn f
  fun i => values[i.val]

@[simp] theorem denseColumn_apply {n : ℕ} (f : Column n) (i : Fin n) :
    denseColumn f i = f i := by simp [denseColumn]

def denseMatrix {m n : ℕ} (f : Coefficients m n) : Coefficients m n :=
  let rows := Vector.ofFn (fun i => Vector.ofFn (f i))
  Matrix.of (fun i j => rows[i.val][j.val])

@[simp] theorem denseMatrix_apply {m n : ℕ} (f : Coefficients m n) (i : Fin m) (j : Fin n) :
    denseMatrix f i j = f i j := by simp [denseMatrix]

def Solves {m n : ℕ} (A : Coefficients m n) (b : Column m) (x : Column n) : Prop :=
  ∀ i, ∑ j, A i j * x j = b i

theorem solves_iff_mulVec {m n : ℕ} {A : Coefficients m n} {b : Column m} {x : Column n} :
    Solves A b x ↔ A.mulVec x = b := by
  unfold Solves Matrix.mulVec dotProduct
  exact funext_iff.symm

def candidates (m n : ℕ) : List (Fin m × Fin n) :=
  (List.finRange m).flatMap fun i => (List.finRange n).map fun j => (i,j)

@[simp] theorem candidates_length (m n : ℕ) : (candidates m n).length = m*n := by
  simp [candidates, List.length_flatMap]

theorem mem_candidates {m n : ℕ} (p : Fin m × Fin n) : p ∈ candidates m n := by
  rcases p with ⟨i,j⟩
  apply List.mem_flatMap.mpr
  exact ⟨i, by simp, List.mem_map.mpr ⟨j, by simp, rfl⟩⟩

def firstPivot {m n : ℕ} (A : Coefficients m n) : Option (Fin m × Fin n) :=
  (candidates m n).find? (fun p => decide (A p.1 p.2 ≠ 0))

theorem firstPivot_ne_zero {m n : ℕ} {A : Coefficients m n} {p : Fin m × Fin n}
    (h : firstPivot A = some p) : A p.1 p.2 ≠ 0 := by
  unfold firstPivot at h
  have hh := List.find?_some h
  exact of_decide_eq_true hh

theorem firstPivot_none {m n : ℕ} {A : Coefficients m n}
    (h : firstPivot A = none) (i : Fin m) (j : Fin n) : A i j = 0 := by
  have hh := (List.find?_eq_none.mp h) (i,j) (mem_candidates (i,j))
  simpa using hh

/-- The unreduced rational multiplier for an available pivot row. -/
def multiplier {m n : ℕ} (A : Coefficients (m+1) (n+1)) (i : Fin (m+1)) (j : Fin (n+1))
    (u : Fin m) : ℚ := A (i.succAbove u) j / A i j

def stepMatrix {m n : ℕ} (A : Coefficients (m+1) (n+1)) (i : Fin (m+1)) (j : Fin (n+1)) :
    Coefficients m n :=
  let c := denseColumn (multiplier A i j)
  denseMatrix (Matrix.of fun u v => A (i.succAbove u) (j.succAbove v) - c u * A i (j.succAbove v))

def stepRhs {m n : ℕ} (A : Coefficients (m+1) (n+1)) (b : Column (m+1))
    (i : Fin (m+1)) (j : Fin (n+1)) : Column m :=
  denseColumn fun u => b (i.succAbove u) - multiplier A i j u * b i

@[simp] theorem stepMatrix_apply {m n : ℕ} (A : Coefficients (m+1) (n+1))
    (i : Fin (m+1)) (j : Fin (n+1)) (u : Fin m) (v : Fin n) :
    stepMatrix A i j u v = A (i.succAbove u) (j.succAbove v) - multiplier A i j u * A i (j.succAbove v) := by
  simp [stepMatrix]

@[simp] theorem stepRhs_apply {m n : ℕ} (A : Coefficients (m+1) (n+1)) (b : Column (m+1))
    (i : Fin (m+1)) (j : Fin (n+1)) (u : Fin m) :
    stepRhs A b i j u = b (i.succAbove u) - multiplier A i j u * b i := by
  simp [stepRhs]

/-- Back substitution of the pivot coordinate and restoration of column order. -/
def restore {m n : ℕ} (A : Coefficients (m+1) (n+1)) (b : Column (m+1))
    (i : Fin (m+1)) (j : Fin (n+1)) (x : Column n) : Column (n+1) :=
  let value := (b i - (List.finRange n).foldl (fun s k => s + A i (j.succAbove k) * x k) 0) / A i j
  denseColumn (Fin.insertNth j value x)

theorem fold_add_eq_sum {α S : Type*} [AddMonoid S] (l : List α) (f : α → S) (s : S) :
    l.foldl (fun z a => z + f a) s = s + (l.map f).sum := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih => simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, add_assoc]

theorem restore_pivot {m n : ℕ} (A : Coefficients (m+1) (n+1)) (b : Column (m+1))
    (i : Fin (m+1)) (j : Fin (n+1)) (x : Column n) :
    restore A b i j x j = (b i - ∑ v, A i (j.succAbove v) * x v) / A i j := by
  simp [restore, fold_add_eq_sum, ← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]

@[simp] theorem restore_other {m n : ℕ} (A : Coefficients (m+1) (n+1)) (b : Column (m+1))
    (i : Fin (m+1)) (j : Fin (n+1)) (x : Column n) (v : Fin n) :
    restore A b i j x (j.succAbove v) = x v := by
  simp [restore]

private theorem schur_sum {m n : ℕ} (A : Coefficients (m+1) (n+1))
    (i : Fin (m+1)) (j : Fin (n+1)) (x : Column n) (u : Fin m) :
    (∑ v, stepMatrix A i j u v * x v) =
      (∑ v, A (i.succAbove u) (j.succAbove v) * x v) -
        multiplier A i j u * ∑ v, A i (j.succAbove v) * x v := by
  simp only [stepMatrix_apply, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]

private theorem split_sum {m n : ℕ} (A : Coefficients m (n+1)) (r : Fin m)
    (j : Fin (n+1)) (x : Column (n+1)) :
    (∑ v, A r v * x v) = A r j * x j + ∑ v, A r (j.succAbove v) * x (j.succAbove v) :=
  Fin.sum_univ_succAbove (fun v => A r v * x v) j

private theorem clear_multiplier {m n : ℕ} {A : Coefficients (m+1) (n+1)}
    {i : Fin (m+1)} {j : Fin (n+1)} (h : A i j ≠ 0) (u : Fin m) :
    multiplier A i j u * A i j = A (i.succAbove u) j := by
  exact div_mul_cancel₀ _ h

theorem solves_step_of_solves {m n : ℕ} {A : Coefficients (m+1) (n+1)} {b : Column (m+1)}
    {i : Fin (m+1)} {j : Fin (n+1)} {x : Column (n+1)} (h : A i j ≠ 0) (hx : Solves A b x) :
    Solves (stepMatrix A i j) (stepRhs A b i j) (fun v => x (j.succAbove v)) := by
  intro u
  rw [schur_sum, stepRhs_apply]
  have hrow := (split_sum A (i.succAbove u) j x).symm.trans (hx (i.succAbove u))
  have htop := (split_sum A i j x).symm.trans (hx i)
  have htop' := congrArg ((multiplier A i j u) * ·) htop
  dsimp only at htop'
  rw [mul_add, ← mul_assoc, clear_multiplier h] at htop'
  linarith only [hrow, htop']

theorem solves_restore {m n : ℕ} {A : Coefficients (m+1) (n+1)} {b : Column (m+1)}
    {i : Fin (m+1)} {j : Fin (n+1)} {x : Column n} (h : A i j ≠ 0)
    (hx : Solves (stepMatrix A i j) (stepRhs A b i j) x) : Solves A b (restore A b i j x) := by
  have htop : A i j * restore A b i j x j + (∑ v, A i (j.succAbove v) * x v) = b i := by
    rw [restore_pivot, mul_comm (A i j), div_mul_cancel₀ _ h]
    ring
  intro u
  induction u using Fin.succAboveCases i with
  | x => rw [split_sum A _ j]; simpa only [restore_other] using htop
  | p u =>
    rw [split_sum A _ j]
    simp only [restore_other]
    have hh := hx u
    rw [schur_sum, stepRhs_apply] at hh
    have htop' := congrArg ((multiplier A i j u) * ·) htop
    dsimp only at htop'
    rw [mul_add, ← mul_assoc, clear_multiplier h] at htop'
    linarith only [hh, htop']

def zeroSolution {m n : ℕ} (b : Column m) : Option (Column n) :=
  if (List.finRange m).all (fun i => decide (b i = 0)) then some 0 else none

private theorem zeroSolution_spec {m n : ℕ} {A : Coefficients m n} {b : Column m}
    (hA : ∀ i j, A i j = 0) :
    ((zeroSolution (n := n) b).isSome ↔ ∃ x, Solves A b x) ∧
      (∀ x, zeroSolution b = some x → Solves A b x) := by
  have hz : (List.finRange m).all (fun i => decide (b i = 0)) = true ↔ ∀ i, b i = 0 := by
    simp [List.all_eq_true]
  have hsol (x : Column n) : Solves A b x ↔ ∀ i, b i = 0 := by
    simp [Solves, hA, eq_comm]
  by_cases hb : ∀ i, b i = 0
  · simp [zeroSolution, hsol, hb]
  · simp [zeroSolution, Bool.eq_false_iff.mpr (fun ht => hb (hz.mp ht)), hsol, hb]

/-- Pivoted rational elimination on a dense rectangular system. -/
def solveCore : (m n : ℕ) → Coefficients m n → Column m → Option (Column n)
  | 0, _, _, _ => some 0
  | _+1, 0, _, b => zeroSolution b
  | m+1, n+1, A, b =>
    match firstPivot A with
    | none => zeroSolution b
    | some (i,j) => (solveCore m n (stepMatrix A i j) (stepRhs A b i j)).map (restore A b i j)

/-- Soundness and completeness, including empty, underdetermined, and
inconsistent systems. -/
theorem solveCore_spec (m n : ℕ) (A : Coefficients m n) (b : Column m) :
    ((solveCore m n A b).isSome ↔ ∃ x, Solves A b x) ∧
      (∀ x, solveCore m n A b = some x → Solves A b x) := by
  induction m generalizing n with
  | zero => simp [solveCore, Solves]
  | succ m ih =>
    cases n with
    | zero => exact zeroSolution_spec (fun _ j => j.elim0)
    | succ n =>
      rw [solveCore]
      cases hp : firstPivot A with
      | none => exact zeroSolution_spec (firstPivot_none hp)
      | some p =>
        obtain ⟨i,j⟩ := p
        dsimp only
        have hz := firstPivot_ne_zero hp
        have H := ih n (stepMatrix A i j) (stepRhs A b i j)
        cases hx : solveCore m n (stepMatrix A i j) (stepRhs A b i j) with
        | none =>
          simp
          intro x h
          have hh := H.1.mpr ⟨_, solves_step_of_solves hz h⟩
          simp [hx] at hh
        | some x =>
          have h := solves_restore hz (H.2 x hx)
          simp only [Option.map_some, Option.isSome_some, true_iff, Option.some.injEq]
          exact ⟨⟨_, h⟩, fun _ he => he ▸ h⟩

end Reconstruction.BareissSolver
