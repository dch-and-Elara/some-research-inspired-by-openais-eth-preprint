
import S11Schedule
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Ring.GeomSum

namespace S11

open scoped BigOperators

/-- The exact generating product used to bound the DFS leaves. -/
noncomputable def generatingProduct (θ : ℝ) (weights : List ℕ) : ℝ :=
  (weights.map fun w : ℕ => (1 - Real.exp (-θ * w))⁻¹).prod

private theorem geom_bound' {q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    (∑ b ∈ Finset.range n, q^b) ≤ (1-q)⁻¹ := by
  rw [← one_div]
  apply (le_div_iff₀ (sub_pos.2 hq1)).2
  have hs := geom_sum_mul q n
  have hpow : 0 ≤ q^n := pow_nonneg hq _
  nlinarith only [hs,hpow]

private theorem generating_pos {θ : ℝ} (hθ : 0 < θ) {ws : List ℕ}
    (hws : ∀ w ∈ ws, 0 < w) : 0 < generatingProduct θ ws := by
  induction ws with
  | nil => simp [generatingProduct]
  | cons w ws ih =>
    have hw : 0 < (w : ℝ) := by exact_mod_cast (hws w (by simp))
    have hq : Real.exp (-θ * w) < 1 := Real.exp_lt_one_iff.2 (by linarith only [mul_pos hθ hw])
    exact mul_pos (inv_pos.mpr (sub_pos.2 hq)) (ih (fun w hw => hws w (by simp [hw])))

theorem tuple_generating_bound {θ : ℝ} (hθ : 0 < θ) (ws : List ℕ)
    (hws : ∀ w ∈ ws, 0 < w) (p : ℕ) :
    ((tuples ws p).length : ℝ) ≤ Real.exp (θ * p) * generatingProduct θ ws := by
  induction ws generalizing p with
  | nil =>
    simp only [tuples, generatingProduct, List.map_nil, List.prod_nil, mul_one]
    split <;> simp only [List.length_nil, List.length_singleton, Nat.cast_zero, Nat.cast_one]
    · positivity
    · apply Real.one_le_exp
      positivity
  | cons w ws ih =>
    have hw := hws w (by simp)
    have htail : ∀ b ∈ ws, 0 < b := fun b hb => hws b (by simp [hb])
    have hwR : 0 < (w : ℝ) := by exact_mod_cast hw
    by_cases hp : p = 0
    · simp only [tuples, hp, ↓reduceIte, List.length_nil, Nat.cast_zero]
      exact (mul_pos (Real.exp_pos _) (generating_pos hθ hws)).le
    simp only [tuples, hp, ↓reduceIte, List.length_flatMap, List.length_map]
    let n := (p-1)/w+1
    let q := Real.exp (-θ * w)
    let G := generatingProduct θ ws
    let c := Real.exp (θ * p)
    have hq : q < 1 := by
      change Real.exp (-θ * w) < 1
      apply Real.exp_lt_one_iff.2
      linarith only [mul_pos hθ hwR]
    have hq0 : 0 ≤ q := (Real.exp_pos _).le
    have hG := (generating_pos hθ htail).le
    have hterm (b : ℕ) (hb : b < n) :
        ((tuples ws (p-w*b)).length : ℝ) ≤ (c*G) * q^b := by
      have hb' : b ≤ (p-1)/w := by dsimp [n] at hb; omega
      have hwb : w*b ≤ p := by
        have h := (Nat.le_div_iff_mul_le hw).1 hb'
        rw [Nat.mul_comm b w] at h
        omega
      refine (ih htail (p-w*b)).trans_eq ?_
      dsimp [c,q,G]
      rw [Nat.cast_sub hwb, Nat.cast_mul, ← Real.exp_nat_mul]
      have he : θ * ((p : ℝ) - w * b) = θ * p + (b : ℝ) * (-θ * w) := by ring
      rw [he, Real.exp_add]
      ring
    rw [Nat.cast_list_sum, List.map_map]
    change (List.map (fun b => ((tuples ws (p - w*b)).length : ℝ)) (List.range n)).sum ≤ _
    rw [← Multiset.sum_coe, ← Multiset.map_coe]
    change (∑ b ∈ Finset.range n, ((tuples ws (p-w*b)).length : ℝ)) ≤ _
    calc
      _ ≤ ∑ b ∈ Finset.range n, (c*G) * q^b := Finset.sum_le_sum fun b hb =>
        hterm b (Finset.mem_range.1 hb)
      _ = (c*G) * ∑ b ∈ Finset.range n, q^b := by rw [Finset.mul_sum]
      _ ≤ (c*G) * (1-q)⁻¹ :=
        mul_le_mul_of_nonneg_left (geom_bound' hq0 hq n) (mul_nonneg (Real.exp_pos _).le hG)
      _ = _ := by
        change (c*G) * (1-q)⁻¹ = c * ((1-q)⁻¹ * G)
        ring

#print axioms tuple_generating_bound

end S11

