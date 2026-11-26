import P5H4MinorTransport
import P5H4Rectangular
import P5H4Degree

/-! Actual monic determinantal gcds of arbitrary rectangular polynomial
matrices. Changing the chart preserves all common divisors, not merely
the final rank in the fraction field. -/
namespace P5H4
open Polynomial Matrix Submodule.IsPrincipal
open scoped BigOperators Classical

variable {K m n : Type*} [Field K]

/-- Generators include repeated indices, which add zero elements only. -/
def minorIdeal (A : Matrix m n K[X]) (s : ℕ) : Ideal K[X] :=
  Ideal.span (Set.range fun p : (Fin s → m) × (Fin s → n) =>
    (A.submatrix p.1 p.2).det)

noncomputable def determinantalGCD (A : Matrix m n K[X]) (s : ℕ) : K[X] :=
  normalize (generator (minorIdeal A s))

theorem dvd_determinantalGCD_iff (A : Matrix m n K[X]) (s : ℕ) (d : K[X]) :
    d ∣ determinantalGCD A s ↔ MinorDivisor A s d := by
  unfold determinantalGCD MinorDivisor
  rw [dvd_normalize_iff, ← Ideal.mem_span_singleton, ← Ideal.span_singleton_le_iff_mem,
    Ideal.span_singleton_generator]
  unfold minorIdeal
  rw [Ideal.span_le]
  constructor
  · intro h u v
    exact Ideal.mem_span_singleton.mp (h ⟨(u,v),rfl⟩)
  · intro h x hx
    rcases hx with ⟨⟨u,v⟩,rfl⟩
    exact Ideal.mem_span_singleton.mpr (h u v)

theorem rowDiagonal_minorDivisor {r : Type*} [DecidableEq r] (e : r ↪ m)
    (a : r → K[X]) (s : ℕ) (d : K[X]) :
    MinorDivisor (rowDiagonal e a) s d ↔ MinorDivisor (diagonal a) s d := by
  have hchart (u : Fin s → r) (v : Fin s → r) :
      (rowDiagonal e a).submatrix (e ∘ u) v = (diagonal a).submatrix u v := by
    apply Matrix.ext
    intro i j
    change (if e (u i) = e (v j) then a (v j) else 0) = _
    by_cases h : u i = v j
    · simp [h]
    · simp [h,e.injective.ne h]
  constructor
  · intro h u v
    simpa only [hchart] using h (e∘u) v
  · intro h u v
    by_cases hpre : ∀ i, ∃ j, u i = e j
    · choose u' he using hpre
      have hu : u = e∘u' := funext he
      rw [hu,hchart]
      exact h u' v
    · push_neg at hpre
      obtain ⟨i,hi⟩ := hpre
      have hz : ((rowDiagonal e a).submatrix u v).det = 0 := by
        apply Matrix.det_eq_zero_of_row_eq_zero i
        intro j
        change (if u i = e (v j) then a (v j) else 0) = 0
        exact if_neg (hi (v j))
      rw [hz]
      exact dvd_zero _

variable [Fintype m] [Fintype n]

omit [Fintype n] in
theorem minorDivisor_left_unit (U : Matrix m m K[X]) (A : Matrix m n K[X])
    (hU : IsUnit U) (s : ℕ) (d : K[X]) :
    MinorDivisor (U*A) s d ↔ MinorDivisor A s d := by
  obtain ⟨u,rfl⟩ := hU
  constructor
  · intro h
    have ht := minorDivisor_left_mul u.inv (u.val*A) s d h
    rwa [← Matrix.mul_assoc,u.inv_val,Matrix.one_mul] at ht
  · exact minorDivisor_left_mul u.val A s d

/-- All common divisors pass across the given actual chart; this version
uses the same chart as the quotient-image profile. -/
theorem chart_minors_of (A : Matrix m n K[X]) {r : ℕ} (e : Fin r ↪ m) (a : Fin r → K[X])
    (U : Matrix m m K[X]) (Z : Matrix m (Fin r) K[X]) (C : Matrix (Fin r) n K[X])
    (T : Matrix n (Fin r) K[X]) (hU : IsUnit U) (hu : U*Z = rowDiagonal e a)
    (hC : Z*C = A) (hT : A*T = Z) (s : ℕ) (d : K[X]) :
    d ∣ determinantalGCD A s ↔
      ∀ u : Fin s → Fin r, Function.Injective u → d ∣ ∏ i, a (u i) := by
  rw [dvd_determinantalGCD_iff]
  have heq : MinorDivisor A s d ↔ MinorDivisor Z s d := by
    constructor
    · intro h
      rw [← hT]
      exact minorDivisor_right_mul A T s d h
    · intro h
      rw [← hC]
      exact minorDivisor_right_mul Z C s d h
  rw [heq,← minorDivisor_left_unit U Z hU,hu,rowDiagonal_minorDivisor]
  exact minorDivisor_diagonal a s d

theorem chart_minors (A : Matrix m n K[X]) :
    ∃ (r : ℕ) (a : Fin r → K[X]), (∀ i, a i ≠ 0) ∧
    ∀ s : ℕ, ∀ d : K[X], d ∣ determinantalGCD A s ↔
      ∀ u : Fin s → Fin r, Function.Injective u → d ∣ ∏ i, a (u i) := by
  obtain ⟨r,e,a,U,Z,C,T,ha,hU,hu,hC,hT⟩ := rectangular_chart A
  exact ⟨r,a,ha,chart_minors_of A e a U Z C T hU hu hC hT⟩
#print axioms dvd_determinantalGCD_iff
#print axioms rowDiagonal_minorDivisor
#print axioms chart_minors_of
#print axioms chart_minors
end P5H4
