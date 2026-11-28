import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-! Finite signed algebra of the mesh point -1 in the acquisition theorem.
The one-port transfer is a literal Boolean affine interpolant. Its paired
version realizes arbitrary row tables on any finite Boolean cube, and then
arbitrary interacting rows in a full finite partition sum. -/

set_option autoImplicit false
set_option warningAsError true

namespace ShiftedAcquisition

open scoped BigOperators

variable {R : Type*} [CommRing R]

/-- The element zero or one represented by a Boolean spin. -/
def spin (x : Bool) : R := if x then 1 else 0

/-- The source's two affine factors. -/
def affine (y : Bool) (a : R) : R := if y then a else 1 - a

/-- The matrix with rows indexed by the old row spin and columns by the matched bit. -/
def shiftMatrix : Bool → Bool → R
  | false, false => 1
  | false, true  => 2
  | true,  false => 0
  | true,  true  => -1

theorem matrix_is_affine (y x : Bool) :
    shiftMatrix (R := R) y x = affine y (-(spin x : R)) := by
  cases y <;> cases x <;> simp [shiftMatrix, affine, spin]
  ring

/-- The literal one-coordinate two-port sum, including the auxiliary pin at one. -/
theorem paired_affine_identity (b : Bool → R) (x : Bool) :
    (∑ y : Bool, ∑ z : Bool,
        b (y && z) * affine y (-(spin x : R)) * affine z (-1 : R)) = b x := by
  cases x <;> simp [affine, spin] <;> ring

def pairWeight (p : Bool × Bool) (x : Bool) : R :=
  shiftMatrix p.1 x * shiftMatrix p.2 true

theorem pair_sum (b : Bool → R) (x : Bool) :
    (∑ p : Bool × Bool, b (p.1 && p.2) * pairWeight p x) = b x := by
  rw [Fintype.sum_prod_type]
  simpa only [pairWeight, matrix_is_affine, spin, Bool.true_eq, if_true, mul_assoc]
    using paired_affine_identity b x

abbrev Word (n : ℕ) := Fin n → Bool
abbrev PairedWord (n : ℕ) := Fin n → Bool × Bool

def rowInput {n : ℕ} (a : PairedWord n) : Word n :=
  fun i => (a i).1 && (a i).2

theorem rowInput_cons {n : ℕ} (p : Bool × Bool) (a : PairedWord n) :
    rowInput (Fin.cons p a) = Fin.cons (p.1 && p.2) (rowInput a) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [rowInput]
  · simp [rowInput]

/-- An actual sum over all assignments to the two physical row ports per coordinate. -/
def shiftedRow {n : ℕ} (f : Word n → R) (x : Word n) : R :=
  ∑ a : PairedWord n, f (rowInput a) * ∏ i, pairWeight (a i) (x i)

theorem sum_first_coordinate {α S : Type*} [Fintype α] [AddCommMonoid S]
    {n : ℕ} (f : (Fin (n + 1) → α) → S) :
    (∑ a, f a) = ∑ h : α, ∑ rest : Fin n → α, f (Fin.cons h rest) := by
  let e := Fin.consEquiv (fun _ : Fin (n + 1) => α)
  calc
    (∑ a, f a) = ∑ p : α × (Fin n → α), f (e p) := (e.sum_comp f).symm
    _ = _ := by rw [Fintype.sum_prod_type]; rfl

/-- The paired transfer realizes any function on the Boolean cube over any commutative ring. -/
theorem shiftedRow_eq : ∀ {n : ℕ} (f : Word n → R) (x : Word n), shiftedRow f x = f x := by
  intro n
  induction n with
  | zero =>
    intro f x
    have hu (a : PairedWord 0) : rowInput a = x := Subsingleton.elim _ _
    simp [shiftedRow, hu]
  | succ n ih =>
    intro f x
    let tail : Word n := Fin.tail x
    calc
      shiftedRow f x =
          ∑ p : Bool × Bool,
            shiftedRow (fun w : Word n => f (Fin.cons (p.1 && p.2) w)) tail *
              pairWeight p (x 0) := by
                unfold shiftedRow
                rw [sum_first_coordinate]
                apply Finset.sum_congr rfl
                intro p _
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro a _
                rw [rowInput_cons, Fin.prod_univ_succ]
                simp only [Fin.cons_zero, Fin.cons_succ]
                change _ = (f (Fin.cons (p.1 && p.2) (rowInput a)) *
                    (∏ j : Fin n, pairWeight (a j) (x j.succ))) * pairWeight p (x 0)
                ac_rfl
      _ = ∑ p : Bool × Bool,
            f (Fin.cons (p.1 && p.2) tail) * pairWeight p (x 0) := by simp only [ih]
      _ = f (Fin.cons (x 0) tail) := pair_sum (fun b => f (Fin.cons b tail)) (x 0)
      _ = f x := congrArg f (Fin.cons_self_tail x)

/-- All local Boolean spins are summed jointly in the left partition function.
The original column assignment can feed any number of rows or several ports
of one row; the theorem imposes no disjointness condition on scope. -/
theorem finite_partition_eq {Vars Rows : Type*} [Fintype Vars] [DecidableEq Vars]
    [Fintype Rows] [DecidableEq Rows] (arity : Rows → ℕ)
    (scope : (r : Rows) → Fin (arity r) → Vars)
    (row : (r : Rows) → Word (arity r) → R) (col : (Vars → Bool) → R) :
    (∑ x : Vars → Bool, col x *
      ∑ a : (r : Rows) → PairedWord (arity r),
        ∏ r : Rows, row r (rowInput (a r)) *
          ∏ i : Fin (arity r), pairWeight (a r i) (x (scope r i))) =
    ∑ x : Vars → Bool, col x * ∏ r : Rows, row r (fun i => x (scope r i)) := by
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  let term (r : Rows) (w : PairedWord (arity r)) : R :=
    row r (rowInput w) * ∏ i : Fin (arity r), pairWeight (w i) (x (scope r i))
  change (∑ a : (r : Rows) → PairedWord (arity r), ∏ r : Rows, term r (a r)) = _
  rw [← Fintype.prod_sum term]
  apply Finset.prod_congr rfl
  intro r _
  exact shiftedRow_eq (row r) (fun i => x (scope r i))

#print axioms matrix_is_affine
#print axioms paired_affine_identity
#print axioms pair_sum
#print axioms rowInput_cons
#print axioms sum_first_coordinate
#print axioms shiftedRow_eq
#print axioms finite_partition_eq

end ShiftedAcquisition
