import AOracleMachine
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Succinct A1 verifier for bounded literal tensors and sparse wires

Input is a list of small physical tensors and sparse local linear
recipes, not a truth table on an entire row or column assignment.
The coefficient recipes may use genuine native kernel cells generated
on demand; this file makes no promise about an arbitrary coefficient
oracle. Variable-degree bounded Boolean tables are stored per vertex.
-/

open scoped BigOperators

namespace AOracleSuccinct
open AOracleWitness AOracleThreshold

/-- Low-coordinate-first rank, executable without enumerating the
Boolean cube. Its output is a legal local table address. -/
def rankBits : {d : ℕ} → (Fin d → Bool) → ℕ
  | 0, _ => 0
  | d+1, a => (a 0).toNat + 2*rankBits (fun i : Fin d => a i.succ)

theorem rankBits_lt {d : ℕ} (a : Fin d → Bool) : rankBits a < 2^d := by
  induction d with
  | zero => simp [rankBits]
  | succ d ih =>
    rw [rankBits, pow_succ]
    have h := ih (fun i : Fin d => a i.succ)
    have hb : (a 0).toNat ≤ 1 := by cases a 0 <;> decide
    omega

theorem rankBits_inj {d : ℕ} : Function.Injective (@rankBits d) := by
  induction d with
  | zero =>
    intro a b _
    funext j
    exact Fin.elim0 j
  | succ d ih =>
    intro a b h
    rw [rankBits, rankBits] at h
    have ht : (a 0).toNat ≤ 1 := by cases a 0 <;> decide
    have hu : (b 0).toNat ≤ 1 := by cases b 0 <;> decide
    have ha : (a 0).toNat = (b 0).toNat := by omega
    have hb : rankBits (fun j : Fin d => a j.succ) =
        rankBits (fun j : Fin d => b j.succ) := by omega
    funext j
    refine Fin.cases ?_ (fun k => congrFun (ih hb) k) j
    cases h1 : a 0 <;> cases h2 : b 0 <;> simp_all

/-- Every original vertex is given by its own literal local entry
table; arbitrary global assignment functions are not input. -/
structure BoolTensor (n delta : ℕ) where
  arity : ℕ
  small : arity ≤ delta
  port : Fin arity → Fin n
  table : Fin (2^arity) → Bool

def BoolTensor.read {n delta : ℕ} (T : BoolTensor n delta)
    (a : Fin n → Bool) : Bool :=
  let localBits := fun j => a (T.port j)
  T.table ⟨rankBits localBits,rankBits_lt localBits⟩

/-- Charge the actual incidence addresses and small truth-table bytes.
An arity header needs to be added separately by a format which stores
each arity explicitly. -/
def BoolTensor.payload {n delta : ℕ} (T : BoolTensor n delta)
    (addrBits : ℕ) : ℕ := 2^T.arity + T.arity*addrBits

theorem BoolTensor.payload_le {n delta : ℕ} (T : BoolTensor n delta)
    (addrBits : ℕ) : T.payload addrBits ≤ 2^delta+delta*addrBits :=
  Nat.add_le_add (Nat.pow_le_pow_right (by decide) T.small)
    (Nat.mul_le_mul_right _ T.small)

section Recipes
variable {R : Type*} [CommRing R]

/-- A sparse linear form reads one original port bit per entry.
The magnitude is not altered when several entries share a port. -/
abbrev Linear (n : ℕ) (R : Type*) := List (Fin n × R)

def linearEval {n : ℕ} (x : Fin n → Bool) : Linear n R → R
  | [] => 0
  | (j,a) :: t => (if x j then a else 0)+linearEval x t

theorem linearEval_eq {n : ℕ} (x : Fin n → Bool) (l : Linear n R) :
    linearEval x l = (l.map (fun ja => if x ja.1 then ja.2 else 0)).sum := by
  induction l with
  | nil => rfl
  | cons ja l ih =>
    rcases ja with ⟨j,a⟩
    simp [linearEval, ih]

def tensorEval {n d : ℕ} (a : Fin n → Bool) : List (BoolTensor n d) → R
  | [] => 1
  | T :: ts => (if T.read a then 1 else 0)*tensorEval a ts

theorem tensorEval_eq {n d : ℕ} (a : Fin n → Bool) (ts : List (BoolTensor n d)) :
    tensorEval (R:=R) a ts = (ts.map (fun T => if T.read a then (1:R) else 0)).prod := by
  induction ts with
  | nil => rfl
  | cons T ts ih => simp [tensorEval, ih]

def tensorBits {n d : ℕ} (addrBits : ℕ) (ts : List (BoolTensor n d)) : ℕ :=
  (ts.map (fun T => T.payload addrBits)).sum

theorem tensorBits_le {n d : ℕ} (addrBits : ℕ) (ts : List (BoolTensor n d)) :
    tensorBits addrBits ts ≤ ts.length*(2^d+d*addrBits) := by
  induction ts with
  | nil => simp [tensorBits]
  | cons T ts ih =>
    change T.payload addrBits + tensorBits addrBits ts ≤
      (ts.length+1)*(2^d+d*addrBits)
    rw [add_mul, one_mul]
    exact (Nat.add_le_add (T.payload_le addrBits) ih).trans_eq (Nat.add_comm _ _)

/-- Coefficient record fields independent of guessed assignments;
a direct native implementation may produce any such field on demand.
The explicit data here are polynomial even when r and c grow. -/
structure Recipes (R : Type*) (r c m delta : ℕ) where
  rows : List (BoolTensor r delta)
  cols : List (BoolTensor c delta)
  localRecipe : Fin r → Linear c R
  cross : Fin r → Fin m → R
  target : Fin r → Fin m → Bool
  moment : Fin m → Linear c R

variable {r c m delta : ℕ}

def rootTerms (L : Recipes R r c m delta) : RootTerms r c m R where
  rowTable y := tensorEval y L.rows
  colTable x := tensorEval x L.cols
  localWire x j := linearEval x (L.localRecipe j)
  crossCoeff := L.cross
  isTarget := L.target
  sourceMoment x k := linearEval x (L.moment k)

/-- Execute for one guessed assignment. Only the chosen local form
or the corresponding source moment is evaluated for each row. -/
def evaluateRow (L : Recipes R r c m delta) (w : Witness r c m) (j : Fin r) : R :=
  match choice (w.2.2 j) with
  | none =>
    let x := linearEval w.2.1 (L.localRecipe j)
    if w.1 j then x else 1-x
  | some k =>
    let cm := (if L.target j k then L.cross j k else 0) * linearEval w.2.1 (L.moment k)
    if w.1 j then cm else 0-cm

def evaluate (L : Recipes R r c m delta) (w : Witness r c m) : R :=
  AOracleMachine.foldProduct (evaluateRow L w)
    (tensorEval w.1 L.rows * tensorEval w.2.1 L.cols)

theorem evaluate_eq (L : Recipes R r c m delta) (w : Witness r c m) :
    evaluate L w = weight (rootTerms L) w := by
  rw [← AOracleMachine.evaluate_eq]
  rfl

/-- The counting verifier has the same accepting paths as before.
No call constructs an assignment-indexed table. -/
def accept {b p : ℕ} (L : Recipes R r c m delta) (beta : Fin m →₀ ℕ)
    (coord : R →+ ZMod (2^p)) (code : Code r c b) (h : Word p) : Bool :=
  match parse code with
  | none => false
  | some w => valid (rootTerms L) beta w && decide (h.val < (coord (evaluate L w)).val)

theorem accept_exact {b p : ℕ} (L : Recipes R r c m delta) (beta : Fin m →₀ ℕ)
    (coord : R →+ ZMod (2^p)) (code : Code r c b) (h : Word p) :
    accept L beta coord code h = AOracleMachine.accept (rootTerms L) beta coord code h := by
  rw [AOracleMachine.accept_exact]
  cases hp : parse code with
  | none => simp [accept, hp]
  | some w => simp [accept, hp, evaluate_eq]

/-- Numeric coefficient storage includes only wire cells, moment
cells, and the at-most-rm crossing coefficient cells. This is
distinct from the length of one Boolean assignment. -/
def numericCells (L : Recipes R r c m delta) : ℕ :=
  (∑ j, (L.localRecipe j).length) + (∑ k, (L.moment k).length) + r*m

omit [CommRing R] in
theorem numericCells_le (L : Recipes R r c m delta) (s t : ℕ)
    (hs : ∀ j, (L.localRecipe j).length ≤ s) (ht : ∀ k, (L.moment k).length ≤ t) :
    numericCells L ≤ r*s + m*t + r*m := by
  unfold numericCells
  apply Nat.add_le_add_right
  apply Nat.add_le_add
  · calc
      _ ≤ ∑ _j : Fin r, s := Finset.sum_le_sum (fun j _ => hs j)
      _ = _ := by simp
  · calc
      _ ≤ ∑ _k : Fin m, t := Finset.sum_le_sum (fun k _ => ht k)
      _ = _ := by simp

def rowLinearReads (L : Recipes R r c m delta) (a : Allocation r m) (j : Fin r) : ℕ :=
  (choice (a j)).elim ((L.localRecipe j).length) (fun k => (L.moment k).length)

def totalLinearReads (L : Recipes R r c m delta) (a : Allocation r m) : ℕ :=
  ∑ j, rowLinearReads L a j

omit [CommRing R] in
/-- An exact schedule count for linear summands; repeated visits are
charged and no shared table of column assignments is assumed. -/
theorem totalLinearReads_le (L : Recipes R r c m delta) (a : Allocation r m) (s : ℕ)
    (hl : ∀ j, (L.localRecipe j).length ≤ s) (hm : ∀ k, (L.moment k).length ≤ s) :
    totalLinearReads L a ≤ r*s := by
  unfold totalLinearReads
  calc
    _ ≤ ∑ _j : Fin r, s := by
      apply Finset.sum_le_sum
      intro j _
      unfold rowLinearReads
      cases h : choice (a j) with
      | none => exact hl j
      | some k => exact hm k
    _ = _ := by simp

/-- All modes can instead be evaluated directly with the full native
linear form for each row. Still only small literal original tables are
used. -/
theorem aggregate_coordinate {p : ℕ} (L : Recipes R r c m delta)
    (full : Fin r → Linear c R) (coord : R →+ ZMod (2^p)) :
    (countQuery (fun w : Rows r × Cols c => some w) (fun _ => true)
      (fun w => coord ((tensorEval w.1 L.rows*tensorEval w.2 L.cols) *
        ∏ j, LiteralPortCompiler.affine (w.1 j) (linearEval w.2 (full j)))) : ZMod (2^p)) =
      coord (∑ y : Rows r, ∑ x : Cols c, (tensorEval y L.rows*tensorEval x L.cols) *
        ∏ j, LiteralPortCompiler.affine (y j) (linearEval x (full j))) :=
  total_coordinate_from_count (fun y => tensorEval y L.rows) (fun x => tensorEval x L.cols)
    (fun x j => linearEval x (full j)) coord

/-- The actual threshold count yields the complete addressed coefficient.
Neither a row-cube nor a column-cube lookup table is part of the
input to this verifier. -/
theorem coefficient_coordinate {b p : ℕ} (L : Recipes R r c m delta) (beta : Fin m →₀ ℕ)
    (coord : R →+ ZMod (2^p)) (fits : m+1 ≤ 2^b) :
    (countVerify (fun z : Code r c b × Word p => accept L beta coord z.1 z.2) :
        ZMod (2^p)) = coord (MvPolynomial.coeff beta (rootPolynomial (rootTerms L))) := by
  have h : (fun z : Code r c b × Word p => accept L beta coord z.1 z.2) =
      verifier parse (valid (rootTerms L) beta) (fun w => coord (weight (rootTerms L) w)) := by
    funext z
    rw [accept_exact, AOracleMachine.accept_exact]
    cases hp : parse z.1 <;> simp [verifier, hp]
  rw [h]
  exact requested_coordinate_from_count (rootTerms L) beta fits (fun _ : Unit => coord) ()

end Recipes

#print axioms rankBits_inj
#print axioms BoolTensor.payload_le
#print axioms tensorBits_le
#print axioms evaluate_eq
#print axioms accept_exact
#print axioms numericCells_le
#print axioms totalLinearReads_le
#print axioms aggregate_coordinate
#print axioms coefficient_coordinate

end AOracleSuccinct

