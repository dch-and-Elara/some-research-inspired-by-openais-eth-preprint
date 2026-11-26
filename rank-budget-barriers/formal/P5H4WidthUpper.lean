import P5H4WidthLower

/-! The least attainable channel width in the actual truncated jet ring,
including matching factorization and transport through polynomial basis
changes. No zero-modulo-one-power minor criterion is assumed. -/
namespace P5H4
open Polynomial Matrix RankBudget
open scoped Classical BigOperators

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

abbrev Survivors (a : n → K[X]) (t : K) (k : ℕ) :=
  {i : n // rootMultiplicity t (a i) < k}

set_option maxHeartbeats 2400000 in
theorem diagonal_width_upper (a : n → K[X]) (ha : ∀ i, a i ≠ 0) (t : K) (k : ℕ) :
    Factors ((X-C t)^k) (diagonal a) (Survivors a t k) := by
  let q : K[X] := (X-C t)^k
  let S := Survivors a t k
  let U : Matrix n S K[X] := Matrix.of fun i j => if i = j.1 then a i else 0
  let V : Matrix S n K[X] := Matrix.of fun j i => if j.1 = i then 1 else 0
  have hx (i : n) : ∃ c : K[X], a i = q*c + (if rootMultiplicity t (a i) < k then a i else 0) := by
    by_cases h : rootMultiplicity t (a i) < k
    · exact ⟨0, by simp [h]⟩
    · obtain ⟨c,hc⟩ := (le_rootMultiplicity_iff (ha i)).1 (Nat.le_of_not_gt h)
      exact ⟨c, by simpa [h] using hc⟩
  choose c hc using hx
  have hdiag (i : n) : (U*V) i i = if rootMultiplicity t (a i) < k then a i else 0 := by
    rw [Matrix.mul_apply]
    by_cases h : rootMultiplicity t (a i) < k
    · rw [if_pos h, Finset.sum_eq_single (⟨i,h⟩ : S)]
      · simp [U,V]
      · intro j _ hj
        have hn : i ≠ j.1 := fun hj' => hj (Subtype.ext hj'.symm)
        simp [U,V,hn]
      · simp
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro j _
      have hn : i ≠ j.1 := fun hj' => h (hj' ▸ j.property)
      simp [U,V,hn]
  have hoff (i j : n) (hij : i ≠ j) : (U*V) i j = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro u _
    by_cases hui : i = u.1
    · have huj : u.1 ≠ j := fun he => hij (hui.trans he)
      simp [U,V,huj]
    · simp [U,V,hui]
  refine ⟨U,V,diagonal c, Matrix.ext fun i j => ?_⟩
  change (diagonal a) i j = q * (diagonal c) i j + (U*V) i j
  by_cases hij : i = j
  · subst j
    rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, hdiag]
    exact hc i
  · simp [Matrix.diagonal_apply_ne _ hij, hoff _ _ hij]

variable {r : Type*} [Fintype r]

omit [DecidableEq n] in
theorem sandwich_width (q : K[X]) (P L R : Matrix n n K[X]) (h : Factors q P r) :
    Factors q (L * P * R) r := by
  obtain ⟨A,B,E,he⟩ := h
  refine ⟨L*A, B*R, L*E*R, ?_⟩
  rw [he]
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

theorem sandwich_width_iff (q : K[X]) (P L R : Matrix n n K[X])
    (hL : IsUnit L) (hR : IsUnit R) :
    Factors q (L*P*R) r ↔ Factors q P r := by
  obtain ⟨l,hl⟩ := hL
  obtain ⟨a,ha⟩ := hR
  subst L
  subst R
  constructor
  · intro h
    have h' := sandwich_width q (l.val*P*a.val) l.inv a.inv h
    have he : l.inv * (l.val*P*a.val) * a.inv = P := by
      calc
        _ = ((l.inv*l.val)*P)*(a.val*a.inv) := by simp only [Matrix.mul_assoc]
        _ = P := by rw [l.inv_val,a.val_inv,Matrix.one_mul,Matrix.mul_one]
    rwa [he] at h'
  · exact sandwich_width q P l.val a.val

/-- Exact minimal width for a fixed diagonal chart; both clauses are
stated on matrices over the actual quotient ring. -/
theorem least_quotient_width (P U V : Matrix n n K[X]) (a : n → K[X])
    (hU : IsUnit U) (hV : IsUnit V) (hm : U*P*V=diagonal a)
    (ha : ∀ i, a i ≠ 0) (t : K) (k : ℕ) :
    Factors ((X-C t)^k) P (Survivors a t k) ∧
      (Factors ((X-C t)^k) P r → Fintype.card (Survivors a t k) ≤ Fintype.card r) := by
  constructor
  · apply (sandwich_width_iff _ P U V hU hV).1
    rw [hm]
    exact diagonal_width_upper a ha t k
  · intro h
    apply diagonal_width_lower a ha t k
    have hf := sandwich_width _ P U V h
    rwa [hm] at hf

theorem exact_width_budget (P U V : Matrix n n K[X]) (a : n → K[X])
    (hU : IsUnit U) (hV : IsUnit V) (hm : U*P*V=diagonal a)
    (ha : ∀ i, a i ≠ 0) (t : K) (k : ℕ) :
    (Fintype.card n - Fintype.card (Survivors a t k)) * k ≤
      Fintype.card n * k - RankBudget.jetLength P t k := by
  obtain ⟨L,R,E,h⟩ := (least_quotient_width (r:=n) P U V a hU hV hm ha t k).1
  have hc := RankBudget.jetLength_of_factor P E L R t k h
  rw [Nat.sub_mul]
  omega

#print axioms diagonal_width_upper
#print axioms sandwich_width_iff
#print axioms least_quotient_width
#print axioms exact_width_budget
end P5H4
