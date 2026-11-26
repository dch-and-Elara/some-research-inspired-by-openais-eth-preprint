import AOracleThreshold
import LiteralPortCompiler
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# Literal A1 verifier for both independent port cubes

Every addressed completed coefficient has one row assignment, one
independent column assignment, and one actual per-row term index in
each witness. The first term index is the local affine branch; other
indices name modes rather than values. Both the target relation and
the exact requested multiplicities are verified. The formal variables
retain the source moments and the row signs.

The layout and finite-precision word operations used to determine the
input functions are supplied. No Turing-machine complexity claim or
hardness of asking this query is built into the result.
-/

open scoped BigOperators

namespace AOracleWitness

open AOracleThreshold

abbrev Rows (r : ℕ) := Fin r → Bool
abbrev Cols (c : ℕ) := Fin c → Bool
abbrev Allocation (r m : ℕ) := Fin r → Fin (m+1)

abbrev Witness (r c m : ℕ) := Rows r × Cols c × Allocation r m
abbrev Code (r c b : ℕ) := Rows r × Cols c × (Fin r → Word b)

/-- Encoding is coordinatewise and independent of the witness weight. -/
def encode {r c m b : ℕ} (fits : m+1 ≤ 2^b) : Witness r c m ↪ Code r c b where
  toFun w := (w.1,w.2.1,fun j => encodeIndex fits (w.2.2 j))
  inj' u v h := by
    refine Prod.ext (congrArg (fun z : Code r c b => z.1) h) (Prod.ext (congrArg (fun z : Code r c b => z.2.1) h) ?_)
    funext j
    exact (encodeIndex fits).injective (congrArg (fun z : Code r c b => z.2.2 j) h)

/-- All fixed-length bit words are possible random guesses. Reject any
out-of-range local/mode field instead of wrapping it or padding its weight. -/
def parse {r c m b : ℕ} (z : Code r c b) : Option (Witness r c m) :=
  if h : ∀ j, (z.2.2 j).val < m+1 then
    some (z.1,z.2.1,fun j => ⟨(z.2.2 j).val,h j⟩)
  else none

theorem parse_encode {r c m b : ℕ} (fits : m+1 ≤ 2^b) (w : Witness r c m) :
    parse (encode fits w) = some w := by
  have hh : ∀ j : Fin r, ((encode fits w).2.2 j).val < m+1 := fun j => (w.2.2 j).isLt
  rw [parse, dif_pos hh]
  rcases w with ⟨y,x,a⟩
  rfl

theorem parse_exact {r c m b : ℕ} (fits : m+1 ≤ 2^b)
    (z : Code r c b) (w : Witness r c m) :
    parse z = some w ↔ z = encode fits w := by
  constructor
  · intro h
    unfold parse at h
    split at h
    · obtain rfl := (Option.some.inj h).symm
      rcases z with ⟨y,x,a⟩
      rfl
    · simp at h
  · rintro rfl
    exact parse_encode fits w

theorem code_card (r c b : ℕ) : Fintype.card (Code r c b) = 2^(r+c+b*r) := by
  simp only [Code, Rows, Cols, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool, ← pow_mul, ← pow_add]
  congr 1
  omega

theorem encoded_counter_bound {r c m b p : ℕ}
    (valid : Witness r c m → Bool) (weight : Witness r c m → ZMod (2^p)) :
    countQuery (parse (r:=r) (c:=c) (m:=m) (b:=b)) valid weight ≤ 2^(r+c+b*r+p) :=
  countQuery_bound _ _ _ (code_card r c b).le

/-- Index zero is the local branch; j.succ records the unique mode j. -/
def choice {m : ℕ} (j : Fin (m+1)) : Option (Fin m) := Fin.cases none some j

theorem choice_zero {m : ℕ} : choice (0:Fin (m+1)) = none := rfl

theorem choice_succ {m : ℕ} (j : Fin m) : choice j.succ = some j := rfl

section Ring

variable {r c m : ℕ} {R : Type*} [CommRing R]
open LiteralPortCompiler MvPolynomial

structure RootTerms (r c m : ℕ) (R : Type*) where
  rowTable : Rows r → R
  colTable : Cols c → R
  localWire : Cols c → Fin r → R
  crossCoeff : Fin r → Fin m → R
  isTarget : Fin r → Fin m → Bool
  sourceMoment : Cols c → Fin m → R

/-- The raw crossing coefficient is not the source moment. -/
def eligibleCoeff (S : RootTerms r c m R) (j : Fin r) (k : Fin m) : R :=
  if S.isTarget j k then S.crossCoeff j k else 0

def picked (S : RootTerms r c m R) (x : Cols c) (y : Rows r) (j : Fin r)
    (a : Option (Fin m)) : R :=
  a.elim (affine (y j) (S.localWire x j))
    (fun k => LiteralPortCompiler.slope (y j) * eligibleCoeff S j k * S.sourceMoment x k)

noncomputable def rowPolynomial (S : RootTerms r c m R) (x : Cols c) (y : Rows r)
    (j : Fin r) : MvPolynomial (Fin m) R :=
  affine (y j)
    (C (S.localWire x j) +
      ∑ k : Fin m, monomial (Finsupp.single k 1) (eligibleCoeff S j k * S.sourceMoment x k))

/-- The completed input polynomial before requesting an exponent tuple. -/
noncomputable def rootPolynomial (S : RootTerms r c m R) : MvPolynomial (Fin m) R :=
  ∑ y : Rows r, ∑ x : Cols c,
    C (S.rowTable y*S.colTable x) * ∏ j, rowPolynomial S x y j

theorem rowPolynomial_sum (S : RootTerms r c m R) (x : Cols c) (y : Rows r)
    (j : Fin r) :
    rowPolynomial S x y j =
      ∑ a : Fin (m+1), monomial (exponent (choice a)) (picked S x y j (choice a)) := by
  have h := portPoly_affine y (fun _ => S.localWire x)
    (fun _ r k => eligibleCoeff S r k*S.sourceMoment x k) j
  unfold rowPolynomial
  rw [← h, Fin.sum_univ_succ]
  simp only [portPoly, exponent, choice_zero, choice_succ, monomial_zero', portTerm, picked,
    Option.elim_none, Option.elim_some]
  apply congrArg (fun z => C (affine (y j) (S.localWire x j)) + z)
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_assoc]

noncomputable def requestedExponent (a : Allocation r m) : Fin m →₀ ℕ :=
  ∑ j, exponent (choice (a j))

/-- Each counter is exactly a sum of Boolean indicators over the row
fields, so forming and comparing the multiplicities needs no enumeration
of complete witness assignments. -/
theorem exponent_count (a : Allocation r m) (k : Fin m) :
    requestedExponent a k = ∑ j, if choice (a j) = some k then (1:ℕ) else 0 := by
  unfold requestedExponent
  rw [Finsupp.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  cases hh : choice (a j) <;> simp [exponent, Finsupp.single_apply]

theorem exponent_le_rows (a : Allocation r m) (k : Fin m) :
    requestedExponent a k ≤ r := by
  rw [exponent_count]
  calc
    _ ≤ ∑ _j : Fin r, (1:ℕ) := by
      apply Finset.sum_le_sum
      intro j _
      split <;> norm_num
    _ = _ := by simp

def allowed (S : RootTerms r c m R) (a : Allocation r m) (j : Fin r) : Bool :=
  (choice (a j)).elim true (S.isTarget j)

def legal (S : RootTerms r c m R) (a : Allocation r m) : Prop :=
  ∀ j, allowed S a j = true

instance (S : RootTerms r c m R) (a : Allocation r m) : Decidable (legal S a) := by
  unfold legal
  exact Fintype.decidableForallFintype

def rowCount (a : Allocation r m) (k : Fin m) : ℕ :=
  ∑ j, if choice (a j) = some k then (1:ℕ) else 0

/-- Compare the m explicit bounded row counters, without computing a
formal Finsupp polynomial inside the verifier. -/
def valid (S : RootTerms r c m R) (β : Fin m →₀ ℕ) (w : Witness r c m) : Bool :=
  decide ((∀ k, rowCount w.2.2 k = β k) ∧ legal S w.2.2)

omit [CommRing R] in
theorem valid_iff (S : RootTerms r c m R) (β : Fin m →₀ ℕ) (w : Witness r c m) :
    valid S β w = true ↔ requestedExponent w.2.2 = β ∧ legal S w.2.2 := by
  rw [valid, decide_eq_true_eq]
  constructor
  · rintro ⟨h,ha⟩
    refine ⟨Finsupp.ext (fun k => ?_), ha⟩
    rw [exponent_count]
    exact h k
  · rintro ⟨h,ha⟩
    refine ⟨fun k => ?_,ha⟩
    rw [rowCount, ← exponent_count, h]

def weight (S : RootTerms r c m R) (w : Witness r c m) : R :=
  (S.rowTable w.1*S.colTable w.2.1) *
    ∏ j, picked S w.2.1 w.1 j (choice (w.2.2 j))

theorem illegal_weight_zero (S : RootTerms r c m R) (w : Witness r c m)
    (h : ¬ legal S w.2.2) : weight S w = 0 := by
  unfold legal at h
  push_neg at h
  obtain ⟨j, hj⟩ := h
  unfold weight
  have hz : picked S w.2.1 w.1 j (choice (w.2.2 j)) = 0 := by
    cases hb : choice (w.2.2 j) with
    | none => simp [allowed,hb] at hj
    | some k =>
      simp only [allowed,hb, Option.elim_some] at hj
      simp [picked, eligibleCoeff, hj]
  rw [Finset.prod_eq_zero (Finset.mem_univ j) hz, mul_zero]

/-- This is the paper's separate source-moment product. Repetitions are
counted exactly once per row assignment, not multiplied by a factorial. -/
theorem pick_moment_product (S : RootTerms r c m R) (x : Cols c) (a : Allocation r m)
    (β : Fin m →₀ ℕ) (hβ : requestedExponent a = β) :
    (∏ j, (choice (a j)).elim 1 (S.sourceMoment x)) =
      modeWeight (S.sourceMoment x) β := by
  rw [← hβ, requestedExponent, modeWeight_sum]

/-- The exact signed sum of accepted formal allocations is the requested
coefficient of the actual two-cube root polynomial. -/
theorem coefficient_eq_valid_sum (S : RootTerms r c m R) (β : Fin m →₀ ℕ) :
    coeff β (rootPolynomial S) =
      ∑ w : Witness r c m, if valid S β w then weight S w else 0 := by
  classical
  simp only [rootPolynomial, rowPolynomial_sum, Fintype.prod_sum, coeff_sum,
    Finset.mul_sum, prod_monomials, C_mul_monomial, coeff_monomial,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun y _ => Finset.sum_congr rfl (fun x _ =>
    Finset.sum_congr rfl (fun a _ => ?_)))
  change (if requestedExponent a = β then weight S (y,x,a) else 0) =
    if valid S β (y,x,a) then weight S (y,x,a) else 0
  by_cases h : requestedExponent a = β
  · by_cases ha : legal S a
    · simp [valid_iff, h, ha]
    · simp [valid_iff, h, ha, illegal_weight_zero S (y,x,a) ha]
  · simp [valid_iff, h]

/-- A single abstract counting-oracle call per additive coefficient
coordinate. The coordinate result is the accepting count reduced
modulo the source power of two. -/
theorem requested_coordinate_from_count {p b : ℕ} {C : Type*}
    (S : RootTerms r c m R) (β : Fin m →₀ ℕ) (fits : m+1 ≤ 2^b)
    (coord : C → R →+ ZMod (2^p)) (i : C) :
    (countQuery (parse (b:=b)) (valid S β) (fun w => coord i (weight S w)): ZMod (2^p)) =
      coord i (coeff β (rootPolynomial S)) := by
  rw [coefficient_eq_valid_sum]
  exact countQuery_coordinate parse (encode fits) (parse_exact fits) _ _ coord i

/-- A1's aggregate evaluation has no allocation guess at all. Here
fullWire is the supplied actual full deformed row form; the two
independent Boolean port cubes and their original tables remain. -/
theorem total_coordinate_from_count {p : ℕ} (rowTable : Rows r → R)
    (colTable : Cols c → R) (fullWire : Cols c → Fin r → R) (coordinate : R →+ ZMod (2^p)) :
    (countQuery (fun w : Rows r × Cols c => some w) (fun _ => true)
      (fun w => coordinate ((rowTable w.1*colTable w.2) *
        ∏ j, affine (w.1 j) (fullWire w.2 j))) : ZMod (2^p)) =
      coordinate (∑ y : Rows r, ∑ x : Cols c, (rowTable y*colTable x) *
        ∏ j, affine (y j) (fullWire x j)) := by
  have he (d w : Rows r × Cols c) : some d = some w ↔ d = Function.Embedding.refl _ w := by
    simp
  simpa only [Fintype.sum_prod_type, if_true] using countQuery_coordinate
    (fun w : Rows r × Cols c => some w) (Function.Embedding.refl _) he (fun _ => true)
    (fun w => (rowTable w.1*colTable w.2) * ∏ j, affine (w.1 j) (fullWire w.2 j))
    (fun _ : Unit => coordinate) ()

end Ring

#print axioms parse_exact
#print axioms code_card
#print axioms exponent_count
#print axioms pick_moment_product
#print axioms coefficient_eq_valid_sum
#print axioms requested_coordinate_from_count
#print axioms total_coordinate_from_count

end AOracleWitness

