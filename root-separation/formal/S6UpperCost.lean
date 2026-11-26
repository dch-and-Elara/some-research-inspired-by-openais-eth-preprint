import S6Upper
import S6Tune

namespace Section6

open Finset
open scoped BigOperators

noncomputable section

lemma taylorCount_pos (n q : ℕ) : 0 < taylorCount n q := by
  apply Nat.lt_of_lt_of_le (show 0 < 2^0*n.choose 0 by simp)
  unfold taylorCount
  have hz : 0 ∈ (range (n+1)).filter (· ≤ q) := by simp
  exact single_le_sum (f := fun j => 2^j*n.choose j) (fun j _ => Nat.zero_le _) hz

/-- The analytic Taylor contribution from the actual truncated pair count. -/
theorem taylor_log_upper (n q : ℕ) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    lg (taylorCount n q) ≤ (q * Real.log (1/η) + (n : ℝ)*(2*η)) / Real.log 2 := by
  have hp : (0 : ℝ) < taylorCount n q := by exact_mod_cast taylorCount_pos n q
  have h := Real.log_le_log (mul_pos (pow_pos hη _) hp) (taylor_generating_upper n q η hη hη1)
  rw [Real.log_mul (pow_pos hη _).ne' hp.ne', Real.log_pow, Real.log_pow] at h
  have hh : Real.log (1 + 2*η) ≤ 2*η := by
    linarith only [Real.log_le_sub_one_of_pos (show 0 < 1+2*η by positivity)]
  have hu := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ n by positivity)
  unfold lg
  apply div_le_div_of_nonneg_right _ logTwo_pos.le
  rw [Real.log_div (by norm_num) hη.ne', Real.log_one, zero_sub]
  linarith only [h, hu]

/-- The three finite exponential contributions. The factor 2Qr accounts
for the two scans and the loops over nodes and groups. -/
theorem literal_log_upper (Q n r q D rows maxGroup : ℕ) (η : ℝ)
    (hQ : 0 < Q) (hr : 0 < r) (hη : 0 < η) (hη1 : η ≤ 1) :
    lg (scanBound Q r (taylorCount n q) D rows maxGroup) ≤
    lg (2 * (Q : ℝ) * r) +
      (q * Real.log (1/η) + (n : ℝ)*(2*η)) / Real.log 2 +
      rows * lg (2 * (D : ℝ)+1) + maxGroup := by
  have hp : (0 : ℝ) < taylorCount n q := by exact_mod_cast taylorCount_pos n q
  have hq : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have h := taylor_log_upper n q η hη hη1
  unfold lg at *
  unfold scanBound
  push_cast
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_mul (by positivity) hp.ne']
  simp only [add_div, mul_div_assoc, div_self logTwo_pos.ne', mul_one]
  simp only [add_div, mul_div_assoc] at h
  linarith only [h]

/-- On a balanced layout, after the verified row and group budgets and the
published scale inequalities, the literal scan has the matching exponent.
This statement counts iterator work; arithmetic and layout construction
are additional polynomial work in the upstream cost contract. -/
theorem balanced_exp_upper (Q n r q D rows maxGroup : ℕ) (η lam ν C d : ℝ)
    (hQ : 0 < Q) (hr : 0 < r) (hη : 0 < η) (hη1 : η ≤ 1)
    (hlam : 0 < lam) (hν : 1 ≤ ν) (hC : 0 ≤ C) (hd : 0 ≤ d)
    (hq : (q : ℝ) ≤ d*n*η)
    (hηs : η ≤ C*ν/√lam) (hlogη : Real.log (1/η) ≤ ν)
    (hrInv : 1/(r : ℝ) ≤ C*ν^2/√lam)
    (hrows : (rows : ℝ) ≤ 2*n/(r*lam))
    (hD : lg (2*(D : ℝ)+1) ≤ lam)
    (hgroup : (maxGroup : ℝ) ≤ 2*n/r) :
    lg (scanBound Q r (taylorCount n q) D rows maxGroup) ≤
      lg (2*(Q : ℝ)*r) + (((d+2)*C/Real.log 2)+4*C)*(n : ℝ)*ν^2/√lam := by
  have hliteral := literal_log_upper Q n r q D rows maxGroup η hQ hr hη hη1
  have hlg0 : 0 ≤ Real.log (1 / η) := Real.log_nonneg ((le_div_iff₀ hη).mpr (by simpa))
  have htaylor : (q * Real.log (1/η) + (n : ℝ)*(2*η)) / Real.log 2 ≤
      ((d+2)*C/Real.log 2)*n*ν^2/√lam := by
    have h₁ : q * Real.log (1/η) ≤ d*n*η*ν :=
      mul_le_mul hq hlogη hlg0 (by positivity)
    have h₂ := mul_le_mul_of_nonneg_right hηs (show 0 ≤ d*(n : ℝ)*ν by positivity)
    have h₃ := mul_le_mul_of_nonneg_left hηs (show 0 ≤ 2*(n : ℝ) by positivity)
    have h₄ := mul_le_mul_of_nonneg_left hν (show 0 ≤ 2*(n : ℝ)*(C*ν/√lam) by positivity)
    apply (div_le_iff₀ logTwo_pos).mpr
    have he : ((d+2)*C/Real.log 2)*n*ν^2/√lam * Real.log 2 =
        (d+2)*C*n*ν^2/√lam := by field_simp [logTwo_pos.ne']
    rw [he]
    ring_nf at h₁ h₂ h₃ h₄ ⊢
    linarith only [h₁,h₂,h₃,h₄]
  have hrow : (rows : ℝ) * lg (2*(D : ℝ)+1) ≤ 2*(n : ℝ)/r := by
    have hlg : 0 ≤ lg (2*(D : ℝ)+1) :=
      div_nonneg (Real.log_nonneg (by linarith [show (0 : ℝ) ≤ D by positivity])) logTwo_pos.le
    have hrp : (0 : ℝ) < r := by exact_mod_cast hr
    calc
      _ ≤ (2*(n : ℝ)/(r*lam)) * lam := mul_le_mul hrows hD hlg (by positivity)
      _ = _ := by field_simp [hrp.ne',hlam.ne']
  have hR := mul_le_mul_of_nonneg_left hrInv (show 0 ≤ 4*(n : ℝ) by positivity)
  ring_nf at hliteral htaylor hrow hgroup hR ⊢
  linarith only [hliteral, htaylor, hrow, hgroup, hR]

#print axioms taylor_log_upper
#print axioms literal_log_upper
#print axioms balanced_exp_upper

end
end Section6





