import BooleanCube.Budget

/-! Paper 1, equation (9), with the literal two endpoints of each maximal
retained interval; the shorter runs are not padded to the global degree. -/

namespace LocalReconstruction.Paper1Coverage

open Polynomial Finset
open scoped BigOperators Polynomial
noncomputable section

structure RetainedRun (q : ℕ) (K : Finset ℕ) (w : ℕ) where
  lo : ℕ
  hi : ℕ
  lo_le : lo ≤ w
  le_hi : w ≤ hi
  hi_le : hi ≤ q
  clear : ∀ k, lo ≤ k → k ≤ hi → k ∉ K
  left_wall : lo = 0 ∨ lo - 1 ∈ K
  right_wall : hi = q ∨ hi + 1 ∈ K

/-- Minimize the left and maximize the right endpoint in the actual interval
containing the retained weight. -/
def actualRetainedRun (q : ℕ) (K : Finset ℕ) (w : ℕ) (hw : w ≤ q) (hK : w ∉ K) :
    RetainedRun q K w := by
  classical
  let ls := (range (w+1)).filter fun n => ∀ j, n ≤ j → j ≤ w → j ∉ K
  let rs := (range (q+1)).filter fun n => w ≤ n ∧ ∀ j, w ≤ j → j ≤ n → j ∉ K
  have lw : w ∈ ls := mem_filter.mpr ⟨mem_range.mpr (by omega), by
    intro j hj₁ hj₂
    rwa [show j = w by omega]⟩
  have rw' : w ∈ rs := mem_filter.mpr ⟨mem_range.mpr (by omega), le_rfl, by
    intro j hj₁ hj₂
    rwa [show j = w by omega]⟩
  let L := ls.min' ⟨w, lw⟩
  let U := rs.max' ⟨w, rw'⟩
  obtain ⟨hLl, hLc⟩ := mem_filter.mp (ls.min'_mem ⟨w, lw⟩)
  obtain ⟨hUq, hUu, hUc⟩ := mem_filter.mp (rs.max'_mem ⟨w, rw'⟩)
  have hL : L ≤ w := Nat.le_of_lt_succ (mem_range.mp hLl)
  have hU : U ≤ q := Nat.le_of_lt_succ (mem_range.mp hUq)
  refine ⟨L, U, hL, hUu, hU, ?_, ?_, ?_⟩
  · intro j lo hi
    by_cases hj : j ≤ w
    · exact hLc j lo hj
    · exact hUc j (by omega) hi
  · by_cases h0 : L = 0
    · exact Or.inl h0
    right
    by_contra hnext
    have prev : L-1 ∈ ls := mem_filter.mpr ⟨mem_range.mpr (by omega), by
      intro j hj₁ hj₂
      by_cases h : L ≤ j
      · exact hLc j h hj₂
      · rwa [show j = L-1 by omega]⟩
    have contra : L ≤ L-1 := ls.min'_le _ prev
    omega
  · by_cases hq : U = q
    · exact Or.inl hq
    right
    by_contra hnext
    have next : U+1 ∈ rs := mem_filter.mpr ⟨mem_range.mpr (by omega), (by omega), by
      intro j hj₁ hj₂
      by_cases h : j ≤ U
      · exact hUc j hj₁ h
      · rwa [show j = U+1 by omega]⟩
    have contra : U+1 ≤ U := rs.le_max' _ next
    omega

/-- Maximal retained runs sharing a retained weight have identical endpoints. -/
theorem RetainedRun.bounds_eq_of_overlap {q w v : ℕ} {K : Finset ℕ}
    (R : RetainedRun q K w) (S : RetainedRun q K v) {x : ℕ}
    (hr₁ : R.lo ≤ x) (hr₂ : x ≤ R.hi)
    (hs₁ : S.lo ≤ x) (hs₂ : x ≤ S.hi) :
    R.lo = S.lo ∧ R.hi = S.hi := by
  have leLeft (R : RetainedRun q K w) (S : RetainedRun q K v)
      (hr₂ : x ≤ R.hi) (hs₁ : S.lo ≤ x) : S.lo ≤ R.lo := by
    by_contra! h
    rcases S.left_wall with h0 | hhit
    · omega
    exact R.clear (S.lo-1) (by omega) (by omega) hhit
  have leRight (R : RetainedRun q K w) (S : RetainedRun q K v)
      (hr₁ : R.lo ≤ x) (hs₂ : x ≤ S.hi) : R.hi ≤ S.hi := by
    by_contra! h
    rcases S.right_wall with hq | hhit
    · have := R.hi_le
      omega
    exact R.clear (S.hi+1) (by omega) (by omega) hhit
  -- The reverse comparisons use the same argument with the two index values exchanged.
  have hl : S.lo ≤ R.lo := leLeft R S hr₂ hs₁
  have hh : R.hi ≤ S.hi := leRight R S hr₁ hs₂
  have hl' : R.lo ≤ S.lo := by
    by_contra! h
    rcases R.left_wall with h0 | hhit
    · omega
    exact S.clear (R.lo-1) (by omega) (by omega) hhit
  have hh' : S.hi ≤ R.hi := by
    by_contra! h
    rcases R.right_wall with hq | hhit
    · have := S.hi_le
      omega
    exact S.clear (R.hi+1) (by omega) (by omega) hhit
  exact ⟨le_antisymm hl' hl, le_antisymm hh hh'⟩

theorem RetainedRun.bounds_eq_of_adjacent {q w v : ℕ} {K : Finset ℕ}
    (R : RetainedRun q K w) (S : RetainedRun q K v) (hv : v = w+1) :
    R.lo = S.lo ∧ R.hi = S.hi := by
  subst v
  have hr : w+1 ≤ R.hi := by
    by_contra! h
    have hEq : R.hi = w := by have := R.le_hi; omega
    rcases R.right_wall with hq | hhit
    · have hw := S.le_hi
      have hq' := S.hi_le
      omega
    · rw [hEq] at hhit
      exact S.clear (w+1) S.lo_le S.le_hi hhit
  exact R.bounds_eq_of_overlap S (R.lo_le.trans (Nat.le_succ w)) hr S.lo_le S.le_hi

/-- The parity polynomial uses precisely the printed nodes `L,…,U`. -/
def actualRunParity (L U : ℕ) : ℚ[X] :=
  Lagrange.interpolate (Icc L U) (fun j : ℕ => (j:ℚ)) (fun j => (-1:ℚ)^j)

theorem actualRunParity_formula (L U : ℕ) :
    actualRunParity L U = ∑ j ∈ Icc L U, C ((-1:ℚ)^j) *
      ∏ l ∈ (Icc L U).erase j, C (((j:ℚ)-(l:ℚ))⁻¹) * (X - C (l:ℚ)) := rfl

private theorem castRat_injective : Function.Injective (fun j : ℕ => (j:ℚ)) := by
  intro i j eq
  change (i:ℚ) = (j:ℚ) at eq
  exact_mod_cast eq

theorem actualRunParity_degree (L U : ℕ) : (actualRunParity L U).natDegree ≤ U-L := by
  apply natDegree_le_of_degree_le
  have h := Lagrange.degree_interpolate_le (s := Icc L U)
    (fun j => (-1:ℚ)^j) castRat_injective.injOn
  rw [Nat.card_Icc] at h
  have e : U+1-L-1 = U-L := by omega
  simpa [actualRunParity, e] using h

theorem actualRunParity_value {L U j : ℕ} (h₁ : L ≤ j) (h₂ : j ≤ U) :
    (actualRunParity L U).eval (j:ℚ) = (-1:ℚ)^j :=
  Lagrange.eval_interpolate_at_node (fun j => (-1:ℚ)^j)
    castRat_injective.injOn (mem_Icc.mpr ⟨h₁, h₂⟩)

private theorem weight_le_dimension {q : ℕ} (s : Cube q) : weight s ≤ q := by
  simpa [weight] using (ones s).card_le_univ

def actualRunArgument {q : ℕ} (a : Fin q → ℚ) (s : Cube q) : ℚ[X] :=
  ∑ i ∈ ones s, (1 - C (a i)⁻¹ * X)

private theorem actualRunArgument_degree {q : ℕ} (a : Fin q → ℚ) (s : Cube q) :
    (actualRunArgument a s).natDegree ≤ 1 := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_sub_le ..).trans
    (max_le (by simp) ((natDegree_C_mul_le ..).trans (by simp)))

private theorem actualRun_ones_flip {q : ℕ} {i : Fin q} {s : Cube q} (h : s i = false) :
    ones (flip i s) = insert i (ones s) := by
  ext j
  by_cases e : j = i
  · subst j
    simp [ones, flip, toggle, oneBit, h]
  · simp [ones, flip, toggle, oneBit, e]

/-- The actual displayed polynomial family in (9), not the padded family
used by the original public `layer_gap_upper`. -/
def literalRunPolynomials {q : ℕ} (a : Fin q → ℚ) (K : Finset ℕ) (s : Cube q) : ℚ[X] :=
  if h : weight s ∈ K then 1 else
    let R := actualRetainedRun q K (weight s) (weight_le_dimension s) h
    C ((-1:ℚ)^(weight s)) * (actualRunParity R.lo R.hi).comp (actualRunArgument a s)

private theorem literalRunPolynomials_clear {q : ℕ} (a : Fin q → ℚ) (K : Finset ℕ)
    (s : Cube q) (hs : weight s ∉ K) :
    let R := actualRetainedRun q K (weight s) (weight_le_dimension s) hs
    literalRunPolynomials a K s =
      C ((-1:ℚ)^(weight s)) * (actualRunParity R.lo R.hi).comp (actualRunArgument a s) := by
  simp [literalRunPolynomials, hs]

theorem literal_run_polynomials_satisfy_eq9 {q : ℕ} {a : Fin q → ℚ}
    (hn : ∀ i, a i ≠ 0) (K : Finset ℕ) :
    edgeCondition a (layerFamily q K) (maxGap q K) (literalRunPolynomials a K) := by
  classical
  have gap := (maxGap_le_iff q (maxGap q K) K).mp le_rfl
  have forward (i : Fin q) (s : Cube q) (hb : s i = false)
      (hs : weight s ∉ K) (ht : weight (flip i s) ∉ K) :
      (literalRunPolynomials a K s).eval (a i) +
        (literalRunPolynomials a K (flip i s)).eval (a i) = 0 := by
    let R := actualRetainedRun q K (weight s) (weight_le_dimension s) hs
    let S := actualRetainedRun q K (weight (flip i s)) (weight_le_dimension (flip i s)) ht
    have hi : i ∉ ones s := by simp [ones, hb]
    have hw : weight (flip i s) = weight s+1 := by
      simp [weight, actualRun_ones_flip hb, hi]
    have bounds := R.bounds_eq_of_adjacent S hw
    have arg : (actualRunArgument a (flip i s)).eval (a i) =
        (actualRunArgument a s).eval (a i) := by
      simp [actualRunArgument, actualRun_ones_flip hb, hi, hn]
      ring
    have pR := literalRunPolynomials_clear a K s hs
    have pS := literalRunPolynomials_clear a K (flip i s) ht
    change literalRunPolynomials a K s =
      C ((-1:ℚ)^(weight s)) * (actualRunParity R.lo R.hi).comp (actualRunArgument a s) at pR
    change literalRunPolynomials a K (flip i s) =
      C ((-1:ℚ)^(weight (flip i s))) * (actualRunParity S.lo S.hi).comp (actualRunArgument a (flip i s)) at pS
    have sign : (-1:ℚ)^(weight (flip i s)) = (-1:ℚ)^(weight s) * (-1) := by
      rw [hw, pow_succ]
    rw [pR, pS, eval_mul, eval_mul, eval_C, eval_C, eval_comp, eval_comp,
      arg, bounds.1, bounds.2, sign]
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro s
    by_cases hs : weight s ∈ K
    · simp [literalRunPolynomials, hs]
    let R := actualRetainedRun q K (weight s) (weight_le_dimension s) hs
    have pR := literalRunPolynomials_clear a K s hs
    change literalRunPolynomials a K s =
      C ((-1:ℚ)^(weight s)) * (actualRunParity R.lo R.hi).comp (actualRunArgument a s) at pR
    rw [pR]
    apply (natDegree_C_mul_le ..).trans
    apply natDegree_comp_le.trans
    exact (Nat.mul_le_mul ((actualRunParity_degree ..).trans
      (gap _ _ (R.lo_le.trans R.le_hi) R.hi_le R.clear)) (actualRunArgument_degree ..)).trans (by simp)
  · intro s
    by_cases hs : weight s ∈ K
    · simp [literalRunPolynomials, hs]
    let R := actualRetainedRun q K (weight s) (weight_le_dimension s) hs
    have pR := literalRunPolynomials_clear a K s hs
    change literalRunPolynomials a K s =
      C ((-1:ℚ)^(weight s)) * (actualRunParity R.lo R.hi).comp (actualRunArgument a s) at pR
    have h0 : (actualRunArgument a s).eval 0 = (weight s:ℚ) := by
      simp [actualRunArgument, eval_finset_sum, weight]
    rw [pR, eval_mul, eval_C, eval_comp, h0, actualRunParity_value R.lo_le R.le_hi, ← mul_pow]
    norm_num
  · intro i s hs ht
    cases h : s i with
    | false => exact forward i s h hs ht
    | true =>
      have inv : flip i (flip i s) = s := (flipEquiv i).left_inv s
      have e := forward i (flip i s) (by simp [flip, toggle, oneBit, h]) ht (by rwa [inv])
      rwa [inv, add_comm] at e

end
end LocalReconstruction.Paper1Coverage

#print axioms LocalReconstruction.Paper1Coverage.actualRetainedRun
#print axioms LocalReconstruction.Paper1Coverage.RetainedRun.bounds_eq_of_overlap
#print axioms LocalReconstruction.Paper1Coverage.RetainedRun.bounds_eq_of_adjacent
#print axioms LocalReconstruction.Paper1Coverage.actualRunParity_formula
#print axioms LocalReconstruction.Paper1Coverage.actualRunParity_degree
#print axioms LocalReconstruction.Paper1Coverage.actualRunParity_value
#print axioms LocalReconstruction.Paper1Coverage.literal_run_polynomials_satisfy_eq9
