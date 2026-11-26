import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

/-! §7 optional finite arithmetic after P.9. This module proves the
exact dyadic series and the backward-induction recurrence majorant.
It does not derive P.7–P.9 from shell geometry or prove the asymptotic
optimization over all native profiles. -/
namespace Paper5.P3
open scoped BigOperators

def shellWeight (j : ℕ) : ℚ := ((j:ℚ)+1)/2^(j+2)

def shellWeightSum (n : ℕ) : ℚ := ∑ j ∈ Finset.range n,shellWeight j

def shellWeightedAffine (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range n,shellWeight j*((n:ℚ)-j+2)

theorem shellWeight_exact (n : ℕ) :
    shellWeightSum n = 1-((n:ℚ)+2)/(2:ℚ)^(n+1) := by
  induction n with
  | zero => norm_num [shellWeightSum]
  | succ n ih =>
    have hs : shellWeightSum (n+1) = shellWeightSum n + shellWeight n := by
      simp only [shellWeightSum,Finset.sum_range_succ]
    rw [hs,ih,shellWeight]
    push_cast
    rw [show (n+1+1:ℕ)=n+2 by omega,pow_succ (2:ℚ) (n+1)]
    field_simp
    ring

theorem shellWeightedAffine_exact (n : ℕ) :
    shellWeightedAffine n = (n:ℚ)-(n:ℚ)/(2:ℚ)^(n+1) := by
  induction n with
  | zero => simp [shellWeightedAffine]
  | succ n ih =>
    have h : shellWeightedAffine (n+1) =
        shellWeightedAffine n + shellWeightSum n + shellWeight n * 3 := by
      unfold shellWeightedAffine shellWeightSum
      rw [Finset.sum_range_succ,←Finset.sum_add_distrib]
      push_cast
      congr 1
      · apply Finset.sum_congr rfl
        intro j _
        ring
      · ring
    rw [h,ih,shellWeight_exact,shellWeight]
    push_cast
    rw [show (n+1+1:ℕ)=n+2 by omega,pow_succ (2:ℚ) (n+1)]
    field_simp
    ring

theorem backward_shell_envelope (B : ℚ) (hB : 0≤B) (g : ℕ→ℚ)
    (h : ∀ n,g n≤B+∑ j ∈ Finset.range n,shellWeight j*g (n-(j+1))) (n : ℕ) :
    g n≤ B*((n:ℚ)+3)/3 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hx := h n
    have hz : ∀ j ∈ Finset.range n,
        shellWeight j*g (n-(j+1)) ≤ B/3*(shellWeight j*((n:ℚ)-j+2)) := by
      intro j hj
      have hn : j<n := Finset.mem_range.mp hj
      have hlt : n-(j+1)<n := by omega
      have h1 := ih (n-(j+1)) hlt
      have hweight : 0≤shellWeight j := by unfold shellWeight; positivity
      have hmul := mul_le_mul_of_nonneg_left h1 hweight
      convert hmul using 1
      rw [Nat.cast_sub (show j+1≤n by omega),Nat.cast_add,Nat.cast_one]
      ring
    have sumH := (Finset.sum_le_sum hz)
    rw [←Finset.mul_sum] at sumH
    change _ ≤ B/3*shellWeightedAffine n at sumH
    rw [shellWeightedAffine_exact] at sumH
    have hsum := hx.trans (add_le_add_left sumH B)
    have hnon : 0≤B/3*((n:ℚ)/(2:ℚ)^(n+1)) := by positivity
    linarith

#print axioms shellWeight_exact
#print axioms shellWeightedAffine_exact
#print axioms backward_shell_envelope
end Paper5.P3
