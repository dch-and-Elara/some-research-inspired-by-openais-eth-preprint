import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

/-!
# J7: source-child moment realization for a partial matching

At the outer zero probe, suppose the partial wiring has at most one matched
port at each subdivision and each original column. Reindex every matched
subdivision by the column it hits. An unmatched subdivision contributes one.
The lemmas verify the remaining finite truth-table sums and their normalized
source moment, conditional on that supplied source layout.
-/

open scoped BigOperators Classical

namespace NativeChildRealization

noncomputable section

section TruthTables

variable {R : Type*} [CommRing R]

def bitValue (R : Type*) [Zero R] [One R] (b : Bool) : R :=
  if b then 1 else 0

def literal (b : Bool) (z : R) : R := if b then z else 1 - z

/-- Sum the original binary equality table at the two deformed arguments. -/
def rowSum (x y : R) : R :=
  ∑ a : Bool, ∑ b : Bool, if a = b then literal a x * literal b y else 0

theorem rowSum_expanded (x y : R) : rowSum x y = (1 - x) * (1 - y) + x * y := by
  simp [rowSum, literal]
  ac_rfl

theorem rowSum_unmatched : rowSum (0 : R) 0 = 1 := by simp [rowSum_expanded]

theorem rowSum_only_left (c : R) (b : Bool) :
    rowSum (c * bitValue R b) 0 = 1 - c * bitValue R b := by simp [rowSum_expanded]

theorem rowSum_only_right (c : R) (b : Bool) :
    rowSum 0 (c * bitValue R b) = 1 - c * bitValue R b := by simp [rowSum_expanded]

/-- An optional record of which equality leg was matched and its column bit.
If the record is absent, both equality arguments are zero. -/
def rowAt (c : R) (s : Option (Bool × Bool)) : R :=
  match s with
  | none => rowSum 0 0
  | some (side, b) => if side then rowSum (c * bitValue R b) 0 else rowSum 0 (c * bitValue R b)

theorem rowAt_reduced (c : R) (s : Option (Bool × Bool)) :
    rowAt c s = match s with
    | none => 1
    | some (_, b) => 1 - c * bitValue R b := by
  cases s with
  | none => exact rowSum_unmatched
  | some a =>
    rcases a with ⟨side, b⟩
    cases side <;> simp [rowAt, rowSum_only_left, rowSum_only_right]

def pinTable (R : Type*) [Zero R] [One R] (sign b : Bool) : R := if b = sign then 1 else 0

theorem unmatched_pin_mass (c : R) (sign : Bool) :
    (∑ b : Bool, pinTable R sign b * rowAt c none) = 1 := by
  cases sign <;> simp [pinTable, rowAt_reduced]

theorem unmatched_pin_bit_numerator (c : R) (sign : Bool) :
    (∑ b : Bool, (pinTable R sign b * rowAt c none) * bitValue R b) = bitValue R sign := by
  cases sign <;> simp [pinTable, bitValue, rowAt_reduced]

end TruthTables

section IndependentTables

variable {K V J : Type*} [Field K] [Fintype V]
variable {U : V → Type*} [∀ v, Fintype (U v)]

def mass (wt : ∀ v, U v → K) (v : V) : K := ∑ z, wt v z

def mean (wt : ∀ v, U v → K) (v : V) (read : U v → K) : K :=
  (∑ z, wt v z * read z) / mass wt v

set_option maxHeartbeats 1000000 in
/-- Marginal of a single column in the full native joint sum. -/
theorem one_column_moment (wt : ∀ v, U v → K) (v : V) (read : U v → K)
    (nonzero : mass wt v ≠ 0) :
    (∑ x : (∀ i, U i), (∏ i, wt i (x i)) * read (x v)) =
      (∏ i, mass wt i) * mean wt v read := by
  let lift : ∀ i, U i → K := fun i z => if h : i = v then read (h ▸ z) else 1
  let norm : V → K := fun i => if i = v then mean wt v read else 1
  have hlift (x : ∀ i, U i) : (∏ i, lift i (x i)) = read (x v) := by
    rw [Finset.prod_eq_single_of_mem v (Finset.mem_univ v)]
    · simp [lift]
    · intro i _ hi
      simp [lift, hi]
  have hnorm : (∏ i, norm i) = mean wt v read := by
    rw [Finset.prod_eq_single_of_mem v (Finset.mem_univ v)]
    · simp [norm]
    · intro i _ hi
      simp [norm, hi]
  have hsum (i : V) : (∑ z : U i, wt i z * lift i z) = mass wt i * norm i := by
    by_cases h : i = v
    · subst i
      have key : mass wt v * ((∑ z, wt v z * read z) / mass wt v) =
          ∑ z, wt v z * read z := by
        field_simp [nonzero]
      simpa [lift, norm, mean] using key.symm
    · simp [lift, norm, h, mass]
  calc
    (∑ x : (∀ i, U i), (∏ i, wt i (x i)) * read (x v)) =
        ∑ x : (∀ i, U i), ∏ i, wt i (x i) * lift i (x i) := by
      simp only [Finset.prod_mul_distrib, hlift]
    _ = ∏ i, ∑ z : U i, wt i z * lift i z :=
      (Fintype.prod_sum (fun i (z : U i) => wt i z * lift i z)).symm
    _ = (∏ i, mass wt i) * mean wt v read := by
      simp only [hsum, Finset.prod_mul_distrib, hnorm]

/-- The exact weighted singleton tile mode, with all independent vertex
normalizations still present. No independence between bits of one vertex is
assumed. Even multiple queried ports of the same vertex are allowed. -/
theorem singleton_source_moment [Fintype J] (wt : ∀ v, U v → K)
    (owner : J → V) (read : ∀ j, U (owner j) → K) (coef : J → K)
    (nonzero : ∀ v, mass wt v ≠ 0) :
    (∑ x : (∀ v, U v), (∏ v, wt v (x v)) *
      ∑ j, coef j * read j (x (owner j))) =
        (∏ v, mass wt v) * ∑ j, coef j * mean wt (owner j) (read j) := by
  calc
    _ = ∑ j, coef j * (∑ x : (∀ v, U v), (∏ v, wt v (x v)) * read j (x (owner j))) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun x _ => ?_
      ac_rfl
    _ = _ := by
      rw [Finset.mul_sum Finset.univ (fun j => coef j * mean wt (owner j) (read j))
        (∏ v, mass wt v)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [one_column_moment wt (owner j) (read j) (nonzero (owner j))]
      ac_rfl

end IndependentTables

/-- The normalized bit in an unmatched original unary pin is exactly its sign. -/
theorem unmatched_pin_mean {K : Type*} [Field K] (c : K) (sign : Bool) :
    (∑ b : Bool, (pinTable K sign b * rowAt c none) * bitValue K b) /
      (∑ b : Bool, pinTable K sign b * rowAt c none) = bitValue K sign := by
  rw [unmatched_pin_bit_numerator, unmatched_pin_mass, div_one]

section PhysicalChild

variable {K V J : Type*} [Field K] [Fintype V]
variable {P : V → Type*} [∀ v, Fintype (P v)]

/-- Each column retains its original Boolean truth table. If it is matched,
attach the subdivision whose selected leg reaches the recorded column port.
The optional unmatched/dummy factor equals one. -/
def nativeWeight (c : K) (table : ∀ v, (P v → Bool) → K)
    (hit : ∀ v, Option (Bool × P v)) (v : V) (z : P v → Bool) : K :=
  table v z * rowAt c ((hit v).map (fun s => (s.1, z s.2)))

theorem nativeZeroMode (c : K) (table : ∀ v, (P v → Bool) → K)
    (hit : ∀ v, Option (Bool × P v)) :
    (∑ x : (∀ v, P v → Bool), (∏ v, table v (x v)) *
      ∏ v, rowAt c ((hit v).map (fun s => (s.1, x v s.2)))) =
    ∏ v, mass (nativeWeight c table hit) v := by
  unfold mass
  rw [Fintype.prod_sum]
  simp only [nativeWeight, Finset.prod_mul_distrib]

/-- J7: from the actual column truth tables and integrated original binary
equality rows to the normalized native source moment. The finite index J can
be the real columns in the requested tile, and coef their exact powers. -/
theorem nativeChildSourceMoment [Fintype J] (c : K)
    (table : ∀ v, (P v → Bool) → K) (hit : ∀ v, Option (Bool × P v))
    (tile : J → Sigma P) (coef : J → K)
    (nonzero : ∀ v, mass (nativeWeight c table hit) v ≠ 0) :
    (∑ x : (∀ v, P v → Bool),
      ((∏ v, table v (x v)) *
        ∏ v, rowAt c ((hit v).map (fun s => (s.1, x v s.2)))) *
      ∑ j, coef j * bitValue K (x (tile j).1 (tile j).2)) =
    (∏ v, mass (nativeWeight c table hit) v) *
      ∑ j, coef j * mean (nativeWeight c table hit) (tile j).1
        (fun z => bitValue K (z (tile j).2)) := by
  simpa only [nativeWeight, Finset.prod_mul_distrib] using
    singleton_source_moment (nativeWeight c table hit) (fun j => (tile j).1)
      (fun j z => bitValue K (z (tile j).2)) coef nonzero

variable [LinearOrder K] [IsStrictOrderedRing K]

omit [Fintype V] in
theorem nativeWeight_mass_positive (c : K) (hc : c < 0)
    (table : ∀ v, (P v → Bool) → K) (hit : ∀ v, Option (Bool × P v))
    (v : V) (nonneg : ∀ z, 0 ≤ table v z) (exists_valid : ∃ z, 0 < table v z) :
    0 < mass (nativeWeight c table hit) v := by
  have hrow (z : P v → Bool) :
      0 < rowAt c ((hit v).map (fun s => (s.1, z s.2))) := by
    cases hit v with
    | none => simp [rowAt_reduced]
    | some s =>
      cases hb : z s.2 with
      | false => simp [rowAt_reduced, bitValue, hb]
      | true =>
        simp [rowAt_reduced, bitValue, hb]
        linarith
  obtain ⟨z, hz⟩ := exists_valid
  exact Finset.sum_pos' (fun u _ => mul_nonneg (nonneg u) (hrow u).le)
    ⟨z, Finset.mem_univ z, mul_pos hz (hrow z)⟩

end PhysicalChild

#print axioms rowSum_expanded
#print axioms rowAt_reduced
#print axioms unmatched_pin_mass
#print axioms unmatched_pin_bit_numerator
#print axioms unmatched_pin_mean
#print axioms one_column_moment
#print axioms singleton_source_moment
#print axioms nativeZeroMode
#print axioms nativeChildSourceMoment
#print axioms nativeWeight_mass_positive

end

end NativeChildRealization
