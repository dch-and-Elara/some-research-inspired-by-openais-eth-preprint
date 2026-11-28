import J3R59Literal
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

/-! Width of the actual R59 global denominator and every cleared entry.
The sole width hypothesis concerns the incoming rational cells, not any
cofactors, intermediate products, pivots or integer representatives. -/
namespace J3R60
open J3R59
open scoped BigOperators

def inputHeight (B : ℕ) (q : ℚ) : Prop :=
  q.num.natAbs ≤ 2^B ∧ q.den ≤ 2^B

theorem rowDen_le {I : Type*} {n B : ℕ} (A : I → Fin n → ℚ) (b : I → ℚ)
    (i : I) (hA : ∀ j, inputHeight B (A i j)) (hb : inputHeight B (b i)) :
    rowDen A b i ≤ 2^(B*(n+1)) := by
  have hp : (∏ j : Fin n, (A i j).den) ≤ (2^B)^n := by
    calc
      _ ≤ ∏ _j : Fin n, 2^B := Finset.prod_le_prod' (fun j _ => (hA j).2)
      _ = _ := by simp
  unfold rowDen
  calc
    _ ≤ 2^B * (2^B)^n := Nat.mul_le_mul hb.2 hp
    _ = _ := by rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, ← Nat.pow_mul, mul_comm]

theorem clearDen_actual_bound {I : Type*} {n B : ℕ}
    (rows : List I) (A : I → Fin n → ℚ) (b : I → ℚ)
    (hA : ∀ i ∈ rows, ∀ j, inputHeight B (A i j))
    (hb : ∀ i ∈ rows, inputHeight B (b i)) :
    clearDen rows A b ≤ 2^(B*((n+1)*rows.length)) := by
  induction rows with
  | nil => simp [clearDen]
  | cons i rs ih =>
    simp only [clearDen, List.map_cons, List.prod_cons, List.length_cons]
    have hrow := rowDen_le A b i (hA i (List.mem_cons_self ..))
      (hb i (List.mem_cons_self ..))
    have htail := ih (fun r hr => hA r (List.mem_cons_of_mem _ hr))
      (fun r hr => hb r (List.mem_cons_of_mem _ hr))
    calc
      _ ≤ 2^(B*(n+1)) * 2^(B*((n+1)*rs.length)) := Nat.mul_le_mul hrow htail
      _ = _ := by
        rw [← Nat.pow_add, Nat.mul_succ]
        congr 1
        ring

theorem scaled_integer_height {d B D : ℕ} {q : ℚ} (divi : q.den ∣ d)
    (hq : q.num.natAbs ≤ 2^B) (hd : d ≤ 2^D) :
    ∃ z : ℤ, (d : ℚ) * q = (z : ℚ) ∧ z.natAbs ≤ 2^(B+D) := by
  obtain ⟨k,hk⟩ := divi
  have hk' : k ≤ d := by
    rw [hk]
    simpa only [one_mul] using
      Nat.mul_le_mul_right k (Nat.one_le_iff_ne_zero.mpr (Rat.den_nz q))
  let z : ℤ := q.num * (k : ℤ)
  refine ⟨z, ?_, ?_⟩
  · have hqd : (q.den : ℚ) * q = q.num := by
      rw [mul_comm]
      exact ((div_eq_iff (Nat.cast_ne_zero.mpr (Rat.den_nz q))).mp
        (Rat.num_div_den q)).symm
    rw [hk, Nat.cast_mul]
    calc
      _ = ((q.den : ℚ)*q)*(k : ℚ) := by ring
      _ = (z : ℚ) := by rw [hqd]; simp [z]
  · dsimp only [z]
    rw [Int.natAbs_mul, Int.natAbs_natCast, Nat.pow_add]
    exact Nat.mul_le_mul hq (hk'.trans hd)

/-- The byte-level clearing algorithm's entry height, for the exact rational
matrix and RHS passed to `J3R59.solveScaled`. -/
theorem actual_starting_integer_height {I : Type*} {n B : ℕ} (rows : List I)
    (A : I → Fin n → ℚ) (b : I → ℚ)
    (hA : ∀ i ∈ rows, ∀ j, inputHeight B (A i j))
    (hb : ∀ i ∈ rows, inputHeight B (b i)) :
    let D := clearDen rows A b
    let L := B + B*((n+1)*rows.length)
    ∀ i ∈ rows,
      (∀ j, ∃ z : ℤ, (D : ℚ) * A i j = z ∧ z.natAbs ≤ 2^L) ∧
      ∃ z : ℤ, (D : ℚ) * b i = z ∧ z.natAbs ≤ 2^L := by
  dsimp only
  have hD := clearDen_actual_bound rows A b hA hb
  intro i hi
  have hp : rowDen A b i ∣ clearDen rows A b :=
    List.dvd_prod (List.mem_map_of_mem (f := rowDen A b) hi)
  constructor
  · intro j
    apply scaled_integer_height _ (hA i hi j).1 hD
    exact dvd_trans (dvd_trans (Finset.dvd_prod_of_mem
      (fun k : Fin n => (A i k).den) (Finset.mem_univ j)) (dvd_mul_left _ _)) hp
  · exact scaled_integer_height (dvd_trans (dvd_mul_right _ _) hp) (hb i hi).1 hD

#print axioms rowDen_le
#print axioms clearDen_actual_bound
#print axioms scaled_integer_height
#print axioms actual_starting_integer_height

end J3R60
