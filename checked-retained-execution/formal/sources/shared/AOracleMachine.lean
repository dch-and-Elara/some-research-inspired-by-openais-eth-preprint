import AOracleWitness
import V9BitCost
import Mathlib.Data.Fin.Tuple.Basic

/-!
# A1 verifier with supplied, charged finite tables

The programs here operate on fixed-width signed-residue coordinate
tables.  Their operation counts are explicit (including multiplicity
checks); table length includes both assignment cubes and every local
coefficient and mode field.  Neither the production of these tables
from a succinct source instance nor the cost of evaluating the counting
oracle itself is included.
-/

open scoped BigOperators

namespace AOracleMachine
open AOracleWitness AOracleThreshold

/-- Distinct addresses of numerical entries, in source-table order.
An eligibility bit is stored separately for each row and mode. -/
abbrev NumAddress (r c m : ℕ) :=
  Rows r ⊕ Cols c ⊕ (Cols c × Fin r) ⊕ (Fin r × Fin m) ⊕ (Cols c × Fin m)

/-- Number of numerical registers in a fully explicit instance. -/
def numRegisters (r c m : ℕ) : ℕ := 2^r + 2^c + 2^c*r + r*m + 2^c*m

theorem register_count (r c m : ℕ) :
    Fintype.card (NumAddress r c m) = numRegisters r c m := by
  simp [NumAddress, Rows, Cols, numRegisters, Nat.add_assoc]

/-- Unpadded data payload: each e-by-ell residue is epℓ bits, the
public monic polynomial has e scalar coefficients, target flags each
have a bit, and each requested multiplicity uses h bits. -/
def payloadBits (r c m e ell p h : ℕ) : ℕ :=
  numRegisters r c m * (e*ell*p) + r*m + e*p + m*h

theorem payload_count (r c m e ell p h : ℕ) :
    Fintype.card ((NumAddress r c m × Fin e × Fin ell × Fin p) ⊕
      (Fin r × Fin m) ⊕ (Fin e × Fin p) ⊕ (Fin m × Fin h))
      = payloadBits r c m e ell p h := by
  calc
    _ = Fintype.card (NumAddress r c m)*(e*ell*p) + r*m + e*p + m*h := by
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      ac_rfl
    _ = _ := by rw [register_count]; rfl

section Program
variable {R : Type*} [CommRing R] {r c m : ℕ}

/-- Static accounting for the executable row/weight schedule; a
lookup accesses one supplied register, not an oracle computation. -/
structure Charge where
  reads : ℕ
  muls : ℕ
  subs : ℕ

instance : Zero Charge := ⟨⟨0,0,0⟩⟩
instance : Add Charge := ⟨fun a b => ⟨a.reads+b.reads, a.muls+b.muls, a.subs+b.subs⟩⟩

def localCharge : Charge := ⟨1,0,1⟩
def crossingCharge : Charge := ⟨2,1,1⟩

/-- Local branch is x or 1-x. Crossing branch is the signed product c*s, so the
signed multiplication in the source is not charged a second product. -/
def evaluateRow (S : RootTerms r c m R) (w : Witness r c m) (j : Fin r) : R :=
  match choice (w.2.2 j) with
  | none =>
    let x := S.localWire w.2.1 j
    if w.1 j then x else 1-x
  | some k =>
    let x := (if S.isTarget j k then S.crossCoeff j k else 0) * S.sourceMoment w.2.1 k
    if w.1 j then x else 0-x

theorem evaluateRow_eq (S : RootTerms r c m R) (w : Witness r c m) (j : Fin r) :
    evaluateRow S w j = picked S w.2.1 w.1 j (choice (w.2.2 j)) := by
  cases hh : choice (w.2.2 j) with
  | none => simp [evaluateRow, hh, picked, LiteralPortCompiler.affine]
  | some k =>
    cases hb : w.1 j <;> cases ht : S.isTarget j k <;>
      simp [evaluateRow, hh, hb, ht, picked, eligibleCoeff, LiteralPortCompiler.slope]

/-- Ordered loop with the two port-table entries as initial accumulator. -/
def foldProduct {n : ℕ} (f : Fin n → R) (acc : R) : R :=
  match n with
  | 0 => acc
  | i+1 => foldProduct (fun j : Fin i => f j.succ) (acc * f 0)

theorem foldProduct_eq {n : ℕ} (f : Fin n → R) (acc : R) :
    foldProduct f acc = acc * ∏ j, f j := by
  induction n generalizing acc with
  | zero => simp [foldProduct]
  | succ i ih => rw [foldProduct, ih, Fin.prod_univ_succ, mul_assoc]

def evaluate (S : RootTerms r c m R) (w : Witness r c m) : R :=
  foldProduct (evaluateRow S w) (S.rowTable w.1 * S.colTable w.2.1)

theorem evaluate_eq (S : RootTerms r c m R) (w : Witness r c m) :
    evaluate S w = weight S w := by
  simp only [evaluate, foldProduct_eq, evaluateRow_eq, weight]

/-- A straight-line execution certificate counting both dedicated port
table reads, crossing table reads, and multiplication chains.  The
eligibility table bits are accounted separately below. -/
def schedule (a : Allocation r m) : Charge :=
  ⟨2 + ∑ j, ((choice (a j)).elim localCharge (fun _ => crossingCharge)).reads,
   1+r + ∑ j, ((choice (a j)).elim localCharge (fun _ => crossingCharge)).muls,
   ∑ j, ((choice (a j)).elim localCharge (fun _ => crossingCharge)).subs⟩

theorem schedule_bound (a : Allocation r m) :
    (schedule a).reads ≤ 2+2*r ∧ (schedule a).muls ≤ 1+2*r ∧ (schedule a).subs ≤ r := by
  have hread : (∑ j, ((choice (a j)).elim localCharge (fun _ => crossingCharge)).reads)
      ≤ ∑ _j : Fin r, 2 := by
    apply Finset.sum_le_sum
    intro j _
    cases choice (a j) <;> simp [localCharge, crossingCharge]
  have hmul : (∑ j, ((choice (a j)).elim localCharge (fun _ => crossingCharge)).muls)
      ≤ ∑ _j : Fin r, 1 := by
    apply Finset.sum_le_sum
    intro j _
    cases choice (a j) <;> simp [localCharge, crossingCharge]
  have hsub : (∑ j, ((choice (a j)).elim localCharge (fun _ => crossingCharge)).subs)
      ≤ ∑ _j : Fin r, 1 := by
    apply Finset.sum_le_sum
    intro j _
    cases choice (a j) <;> simp [localCharge, crossingCharge]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_id] at hread hmul hsub
  rw [Nat.mul_comm r 2] at hread
  simp only [schedule]
  omega

/-- Ordered loop which computes each source multiplicity by adding
one Boolean indicator for each row. Every nested prefix uses <=r. -/
def countPrefix (a : Allocation r m) (k : Fin m) (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | n+1 => countPrefix a k n + (if h : n < r then
      if choice (a ⟨n,h⟩) = some k then 1 else 0 else 0)

theorem countPrefix_le (a : Allocation r m) (k : Fin m) (n : ℕ) :
    countPrefix a k n ≤ n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    rw [countPrefix]
    split
    · split <;> omega
    · omega

def test (S : RootTerms r c m R) (beta : Fin m →₀ ℕ) (w : Witness r c m) : Bool :=
  decide ((∀ k, rowCount w.2.2 k = beta k) ∧ legal S w.2.2)

omit [CommRing R] in
theorem test_eq (S : RootTerms r c m R) (beta : Fin m →₀ ℕ) (w : Witness r c m) :
    test S beta w = valid S beta w := rfl

/-- The executable signed-weight verifier, with its final p-bit strict
comparison. It implements the actual threshold-oracle predicate. -/
def accept {b p : ℕ} (S : RootTerms r c m R) (beta : Fin m →₀ ℕ)
    (coord : R →+ ZMod (2^p)) (code : Code r c b) (threshold : Word p) : Bool :=
  match parse code with
  | none => false
  | some w => test S beta w && decide (threshold.val < (coord (evaluate S w)).val)

theorem accept_exact {b p : ℕ} (S : RootTerms r c m R) (beta : Fin m →₀ ℕ)
    (coord : R →+ ZMod (2^p)) (code : Code r c b) (threshold : Word p) :
    accept S beta coord code threshold =
      match parse code with
      | none => false
      | some w => valid S beta w && decide (threshold.val < (coord (weight S w)).val) := by
  simp only [accept, test_eq, evaluate_eq]

end Program

/-- A scanner which reads the entire supplied payload each time has at
most this explicit monotone bit budget in the specified serial
word model. Ring multiplication is handled by a separate double-basis
schedule; lookup overhead here pessimistically rescans the payload.
No constant-time oracle table access or circuit for a succinct input
is assumed. -/
def serialEnvelope (r c m b h p payload ringWidth ringMul : ℕ) : ℕ :=
  (2+3*r)*(payload+1)*(r+c+b+h+ringWidth+1) +
  (1+2*r)*ringMul + r*(ringWidth+1) +
  (r*m+m+r+1)*(r+c+b+h+p+1)

/-- In particular polynomial in bounded headers, payload, and register
primitive costs. The degree and constant are explicit and do not
depend on the number of nondeterministic paths. -/
theorem serialEnvelope_poly (r c m b h p payload ringWidth ringMul : ℕ) :
    serialEnvelope r c m b h p payload ringWidth ringMul ≤
      10*(r+c+m+b+h+p+payload+ringWidth+ringMul+1)^3 := by
  let z := r+c+m+b+h+p+payload+ringWidth+ringMul+1
  have hz : 1 ≤ z := by dsimp [z]; omega
  have h1 : 2+3*r ≤ 3*z := by dsimp [z]; omega
  have h2 : payload+1 ≤ z := by dsimp [z]; omega
  have h3 : r+c+b+h+ringWidth+1 ≤ z := by dsimp [z]; omega
  have h4 : 1+2*r ≤ 2*z := by dsimp [z]; omega
  have h5 : ringMul ≤ z := by dsimp [z]; omega
  have h6 : r ≤ z := by dsimp [z]; omega
  have h7 : ringWidth+1 ≤ z := by dsimp [z]; omega
  have h8 : r*m+m+r+1 ≤ z*z := by
    simpa [Nat.add_mul, Nat.mul_add, mul_one, one_mul, Nat.add_assoc,
      Nat.add_left_comm, Nat.add_comm] using
      Nat.mul_le_mul (show r+1 ≤ z by dsimp [z]; omega) (show m+1 ≤ z by dsimp [z]; omega)
  have h9 : r+c+b+h+p+1 ≤ z := by dsimp [z]; omega
  have ha := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have hb := Nat.mul_le_mul h4 h5
  have hc := Nat.mul_le_mul h6 h7
  have hd := Nat.mul_le_mul h8 h9
  have he : z*z ≤ z*z*z := by simpa using Nat.mul_le_mul_left (z*z) hz
  change _ ≤ 10*z^3
  unfold serialEnvelope
  nlinarith

#print axioms register_count
#print axioms payload_count
#print axioms evaluate_eq
#print axioms schedule_bound
#print axioms countPrefix_le
#print axioms accept_exact
#print axioms serialEnvelope_poly

end AOracleMachine

