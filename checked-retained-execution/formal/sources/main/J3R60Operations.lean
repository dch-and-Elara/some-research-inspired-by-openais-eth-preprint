import J3R59Literal
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option warningAsError true

/-! Ordered scan and scalar entry visits of the exact R59 recurrence.
The ledger charges an eagerly materialized residual table plus the saved
triangular backsolve, not arbitrary evaluation of Lean closures. -/
namespace J3R60
open J3R59

def paidFirst {I : Type*} (f : I → Bool) : List I → Option I × ℕ
  | [] => (none,0)
  | i :: is => if f i then (some i,1) else
      let q := paidFirst f is
      (q.1,q.2+1)

theorem paidFirst_result {I : Type*} (f : I → Bool) (is : List I) :
    (paidFirst f is).1 = is.find? f := by
  induction is with
  | nil => rfl
  | cons i js ih =>
    rw [paidFirst, List.find?_cons]
    split <;> simp_all

theorem paidFirst_visits {I : Type*} (f : I → Bool) (is : List I) :
    (paidFirst f is).2 ≤ is.length := by
  induction is with
  | nil => simp [paidFirst]
  | cons i js ih =>
    rw [paidFirst]
    split <;> simp_all

structure OpLedger where
  pivotTests : ℕ
  forwardCells : ℕ
  backTerms : ℕ
  backPivots : ℕ

def recordRound {n : ℕ} {I : Type*} (m tested : ℕ)
    (rest : Option (Fin n → ℚ) × OpLedger)
    (A : I → Fin (n+1) → ℚ) (b : I → ℚ) (p : I) :
    Option (Fin (n+1) → ℚ) × OpLedger :=
  (rest.1.map (fun x => join (backHead A b p x) x),
    ⟨tested + rest.2.pivotTests, m*(n+1) + rest.2.forwardCells,
      (if rest.1.isSome then n else 0) + rest.2.backTerms,
      (if rest.1.isSome then 1 else 0) + rest.2.backPivots⟩)

def measuredSolve {I : Type*} (rows : List I) :
    (n : ℕ) → (I → Fin n → ℚ) → (I → ℚ) → ℚ →
      Option (Fin n → ℚ) × OpLedger
  | 0, _, _, _ => (some (fun j => Fin.elim0 j), ⟨0,0,0,0⟩)
  | n+1, A, b, prev =>
      let p := paidFirst (fun r => decide (A r 0 ≠ 0)) rows
      match p.1 with
      | none => (none,⟨p.2,0,0,0⟩)
      | some i => recordRound rows.length p.2
          (measuredSolve rows n (tailMatrix A i prev) (tailRhs A b i prev) (A i 0)) A b i

theorem measured_solve_same_actual_recurrence {I : Type*} (rows : List I) (n : ℕ)
    (A : I → Fin n → ℚ) (b : I → ℚ) (prev : ℚ) :
    (measuredSolve rows n A b prev).1 = fractionFree rows n A b prev := by
  induction n generalizing b prev with
  | zero => rfl
  | succ n ih =>
    simp only [measuredSolve, fractionFree, paidFirst_result]
    cases h : rows.find? (fun r => decide (A r 0 ≠ 0)) with
    | none => rfl
    | some p =>
      simp only [recordRound, ih]

def eliminationTriangle : ℕ → ℕ
  | 0 => 0
  | n+1 => n+1 + eliminationTriangle n

def backTriangle : ℕ → ℕ
  | 0 => 0
  | n+1 => n + backTriangle n

theorem eliminationTriangle_exact (n : ℕ) : 2 * eliminationTriangle n = n*(n+1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [eliminationTriangle, Nat.mul_add, ih]
    ring

theorem backTriangle_exact (n : ℕ) : 2 * backTriangle n = n*(n-1) := by
  cases n with
  | zero => rfl
  | succ n =>
    have he : backTriangle (n+1) = eliminationTriangle n := by
      induction n with
      | zero => rfl
      | succ n ih => rw [backTriangle, ih, eliminationTriangle]
    rw [he, eliminationTriangle_exact]
    simp [Nat.mul_comm]

/-- Exact per-cell visits on a successful run, with actual ordered-pivot
prefix tests rather than a supplied number of tests. -/
theorem measured_success_counts {I : Type*} (rows : List I) (n : ℕ)
    (A : I → Fin n → ℚ) (b : I → ℚ) (prev : ℚ)
    (ok : (measuredSolve rows n A b prev).1.isSome = true) :
    let C := (measuredSolve rows n A b prev).2
    C.forwardCells = rows.length * eliminationTriangle n ∧
      C.backTerms = backTriangle n ∧ C.backPivots = n ∧
      C.pivotTests ≤ n*rows.length := by
  induction n generalizing b prev with
  | zero => simp [measuredSolve, eliminationTriangle, backTriangle]
  | succ n ih =>
    let test : I → Bool := fun r => decide (A r 0 ≠ 0)
    cases h : (paidFirst test rows).1 with
    | none =>
      have hfail : (measuredSolve rows (n+1) A b prev).1.isSome = false := by
        simp only [measuredSolve]
        change (match (paidFirst test rows).1 with
          | none => (none, (⟨(paidFirst test rows).2,0,0,0⟩ : OpLedger))
          | some i => recordRound rows.length (paidFirst test rows).2
                (measuredSolve rows n (tailMatrix A i prev) (tailRhs A b i prev) (A i 0)) A b i).1.isSome
                  = false
        rw [h]
        rfl
      rw [hfail] at ok
      contradiction
    | some p =>
      let S := measuredSolve rows n (tailMatrix A p prev) (tailRhs A b p prev) (A p 0)
      have hs : measuredSolve rows (n+1) A b prev =
          recordRound rows.length (paidFirst test rows).2 S A b p := by
        unfold measuredSolve
        change (match (paidFirst test rows).1 with
          | none => (none, (⟨(paidFirst test rows).2,0,0,0⟩ : OpLedger))
          | some i => recordRound rows.length (paidFirst test rows).2
                (measuredSolve rows n (tailMatrix A i prev) (tailRhs A b i prev) (A i 0)) A b i) = _
        rw [h]
      have hS : S.1.isSome = true := by
        rw [hs] at ok
        simpa only [recordRound, Option.isSome_map] using ok
      have bounds := ih (tailMatrix A p prev) (tailRhs A b p prev) (A p 0) hS
      change S.2.forwardCells = rows.length * eliminationTriangle n ∧
        S.2.backTerms = backTriangle n ∧ S.2.backPivots = n ∧
        S.2.pivotTests ≤ n*rows.length at bounds
      obtain ⟨hc, ht, hp, hv⟩ := bounds
      dsimp only
      rw [hs]
      change rows.length*(n+1) + S.2.forwardCells = rows.length*eliminationTriangle (n+1) ∧
        (if S.1.isSome then n else 0) + S.2.backTerms = backTriangle (n+1) ∧
        (if S.1.isSome then 1 else 0) + S.2.backPivots = n+1 ∧
        (paidFirst test rows).2 + S.2.pivotTests ≤ (n+1)*rows.length
      rw [hS, hc, ht, hp, eliminationTriangle, backTriangle]
      exact ⟨(Nat.mul_add rows.length (n+1) (eliminationTriangle n)).symm,
        rfl, Nat.add_comm 1 n, by
        have hscan := paidFirst_visits test rows
        rw [Nat.succ_mul]
        omega⟩

def measuredScaled {I : Type*} (rows : List I) {n : ℕ}
    (A : I → Fin n → ℚ) (b : I → ℚ) : Option (Fin n → ℚ) × OpLedger :=
  let D : ℚ := (clearDen rows A b : ℚ)
  measuredSolve rows n (fun i j => D*A i j) (fun i => D*b i) 1

theorem measuredScaled_result {I : Type*} (rows : List I) {n : ℕ}
    (A : I → Fin n → ℚ) (b : I → ℚ) :
    (measuredScaled rows A b).1 = solveScaled rows A b := by
  simp only [measuredScaled, solveScaled, measured_solve_same_actual_recurrence]

#print axioms paidFirst_result
#print axioms paidFirst_visits
#print axioms eliminationTriangle_exact
#print axioms backTriangle_exact
#print axioms measured_solve_same_actual_recurrence
#print axioms measured_success_counts
#print axioms measuredScaled_result

end J3R60
