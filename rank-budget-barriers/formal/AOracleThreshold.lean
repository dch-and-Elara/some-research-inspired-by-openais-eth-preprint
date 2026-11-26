import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Fixed-width signed counting interface (A1)

Weights in an A1 witness may be negative or live in an algebra over
Z/(2^p). A p-bit threshold is compared to the *least nonnegative*
coordinate residue, not to an integer lift chosen by sign. The proof
gives a finite, unweighted verifier count; it does not assign a run
time to the counting oracle or to evaluating an original input entry.
-/

open scoped BigOperators

namespace AOracleThreshold

/-- Exactly one unsigned code for each n-bit value, including leading zeros. -/
abbrev Word (n : ℕ) := Fin (2^n)

def decodeIndex (n q : ℕ) (d : Word n) : Option (Fin q) :=
  if h : d.val < q then some ⟨d.val,h⟩ else none

def encodeIndex {n q : ℕ} (fits : q ≤ 2^n) : Fin q ↪ Word n where
  toFun a := Fin.castLE fits a
  inj' _ _ h := Fin.ext (congrArg (fun z : Word n => z.val) h)

theorem decodeIndex_exact {n q : ℕ} (fits : q ≤ 2^n) (d : Word n) (a : Fin q) :
    decodeIndex n q d = some a ↔ d = encodeIndex fits a := by
  unfold decodeIndex
  split
  · constructor
    · intro h
      exact Fin.ext (congrArg (fun z : Fin q => z.val) (Option.some.inj h))
    · intro h
      apply congrArg some
      exact Fin.ext (congrArg (fun z : Word n => z.val) h)
  · rename_i h
    constructor
    · simp
    · intro he
      have hv : d.val = a.val := congrArg (fun z : Word n => z.val) he
      exact False.elim (h (by rw [hv]; exact a.isLt))

/-- The fixed-width source option field need not have a power-of-two alphabet. -/
theorem min_width_fits (q : ℕ) : q ≤ (2:ℕ)^(Nat.clog 2 q) :=
  Nat.le_pow_clog (by decide) q

/-- Count accepts, not distinct output or residue values. -/
def countVerify {D : Type*} [Fintype D] (f : D → Bool) : ℕ :=
  (Finset.univ.filter fun d => f d = true).card

theorem countVerify_sum {D : Type*} [Fintype D] (f : D → Bool) :
    countVerify f = ∑ d, if f d = true then (1:ℕ) else 0 := by
  simp [countVerify]

theorem threshold_card (p w : ℕ) (hw : w ≤ 2^p) :
    countVerify (fun d : Word p => decide (d.val < w)) = w := by
  let e : {d : Word p // d.val < w} ≃ Fin w :=
    { toFun := fun d => ⟨d.val.val,d.2⟩
      invFun := fun d => ⟨Fin.castLE hw d,d.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [countVerify, ← Fintype.subtype_card _ (p := fun d : Word p => d.val < w)]
  · rw [Fintype.card_eq_nat_card, Nat.card_congr e, Nat.card_fin]
  · intro d
    simp

section Parse

variable {D W : Type*} [Fintype D] [Fintype W]

/-- Reindex a total fixed-width code cube by its valid parses. Invalid
codes contribute zero and no valid witness contributes twice. -/
theorem sum_parse_exact {S : Type*} [AddCommMonoid S]
    (parse : D → Option W) (encode : W ↪ D)
    (exactly : ∀ d w, parse d = some w ↔ d = encode w) (f : W → S) :
    (∑ d, (parse d).elim 0 f) = ∑ w, f w := by
  classical
  symm
  calc
    _ = ∑ d ∈ (Finset.univ : Finset W).map encode, (parse d).elim 0 f := by
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl (fun w _ => ?_)
      rw [(exactly (encode w) w).mpr rfl]
      rfl
    _ = _ := by
      apply Finset.sum_subset (by simp)
      intro d _ hd
      cases hparse : parse d with
      | none => rfl
      | some w =>
        exfalso
        exact hd (Finset.mem_map.mpr ⟨w,Finset.mem_univ _,(exactly d w).mp hparse |>.symm⟩)

def verifier {p : ℕ} (parse : D → Option W) (valid : W → Bool)
    (weight : W → ZMod (2^p)) (code : D × Word p) : Bool :=
  match parse code.1 with
  | none => false
  | some w => valid w && decide (code.2.val < (weight w).val)

/-- The integer name of the single finite counting query. -/
def countQuery {p : ℕ} (parse : D → Option W) (valid : W → Bool)
    (weight : W → ZMod (2^p)) : ℕ :=
  countVerify (verifier parse valid weight)

/-- The nonnegative accepting-path count is exactly the sum of least
nonnegative residues of valid weights. This does not assume away carries. -/
theorem countQuery_eq {p : ℕ} (parse : D → Option W) (encode : W ↪ D)
    (exactly : ∀ d w, parse d = some w ↔ d = encode w)
    (valid : W → Bool) (weight : W → ZMod (2^p)) :
    countQuery parse valid weight = ∑ w, if valid w then (weight w).val else 0 := by
  haveI : NeZero ((2:ℕ)^p) := ⟨by positivity⟩
  rw [countQuery, countVerify_sum, Fintype.sum_prod_type]
  calc
    _ = ∑ d, (parse d).elim 0 (fun w => if valid w then (weight w).val else 0) := by
      apply Finset.sum_congr rfl
      intro d _
      cases hp : parse d with
      | none => simp [verifier,hp]
      | some w =>
        cases hv : valid w
        · simp [verifier,hp,hv]
        · simp only [verifier,hp,hv, Bool.true_and, Option.elim_some, if_true]
          rw [← countVerify_sum]
          exact threshold_card p _ (ZMod.val_lt _).le
    _ = _ := sum_parse_exact parse encode exactly _

/-- Reduction of the accepting count recovers the coordinate, even
when the original witnesses had signed integer weights. -/
theorem countQuery_residue {p : ℕ} (parse : D → Option W) (encode : W ↪ D)
    (exactly : ∀ d w, parse d = some w ↔ d = encode w)
    (valid : W → Bool) (weight : W → ZMod (2^p)) :
    (countQuery parse valid weight : ZMod (2^p)) =
      ∑ w, if valid w then weight w else 0 := by
  rw [countQuery_eq parse encode exactly, Nat.cast_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  cases valid w <;> simp

theorem countQuery_signed {p : ℕ} (parse : D → Option W) (encode : W ↪ D)
    (exactly : ∀ d w, parse d = some w ↔ d = encode w)
    (valid : W → Bool) (weight : W → ℤ) :
    (countQuery parse valid (fun w => (weight w : ZMod (2^p))) : ZMod (2^p)) =
      ((∑ w, if valid w then weight w else 0 : ℤ): ZMod (2^p)) := by
  rw [countQuery_residue parse encode exactly, Int.cast_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  cases valid w <;> simp

/-- Extension and truncation coordinates are treated additively.
There is precisely one verifier call per chosen receiving coordinate;
no scalar collapse or unsigned assumption is used in passing the sum. -/
theorem countQuery_coordinate {R C : Type*} [AddCommMonoid R]
    {p : ℕ} (parse : D → Option W) (encode : W ↪ D)
    (exactly : ∀ d w, parse d = some w ↔ d = encode w)
    (valid : W → Bool) (weight : W → R) (coord : C → R →+ ZMod (2^p)) (i : C) :
    (countQuery parse valid (fun w => coord i (weight w)) : ZMod (2^p)) =
      coord i (∑ w, if valid w then weight w else 0) := by
  rw [countQuery_residue parse encode exactly, map_sum]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  cases valid w <;> simp

end Parse

/-- Quantitative witness-width bound: the padded bits are guessed once,
but rejected when they do not parse, so they don't inflate the count. -/
theorem countQuery_bound {D W : Type*} [Fintype D] [Fintype W]
    {p B : ℕ} (parse : D → Option W) (valid : W → Bool)
    (weight : W → ZMod (2^p)) (hD : Fintype.card D ≤ 2^B) :
    countQuery parse valid weight ≤ 2^(B+p) := by
  unfold countQuery countVerify
  have hc : Fintype.card (D × Word p) ≤ 2^(B+p) := by
    rw [Fintype.card_prod, Fintype.card_fin, pow_add]
    exact Nat.mul_le_mul_right _ hD
  exact (Finset.card_le_univ _).trans hc

#print axioms decodeIndex_exact
#print axioms threshold_card
#print axioms sum_parse_exact
#print axioms countQuery_eq
#print axioms countQuery_signed
#print axioms countQuery_coordinate
#print axioms countQuery_bound

end AOracleThreshold

