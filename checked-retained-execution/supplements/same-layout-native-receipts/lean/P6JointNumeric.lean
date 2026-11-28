import J7R13Endpoints

namespace Paper6JointSeating
open J7PrintedParams

theorem enlargedMatchingMargin {N D L : ℕ} (hD : 0<D) (hL : 131072≤L)
    (p2 : L*D≤24*N) :
    4*(bUpper N D L:ℚ) + ((⌈delta N D⌉ : ℤ).toNat : ℚ) + delta N D ≤
      (mu N D - pinMeanUpper N D - 2*rho N D)*(1/2:ℚ)^5 := by
  have hDq : (0:ℚ)<D := by exact_mod_cast hD
  have hLq : (131072:ℚ)≤L := by exact_mod_cast hL
  have hLpos : (0:ℚ)<L := by linarith
  have hμL : (L:ℚ) ≤ mu N D := by
    apply (le_div_iff₀ hDq).2
    exact_mod_cast p2
  have hμ : 0≤mu N D := by linarith
  have hround := (upper_rounding (2*mu N D/L) (by positivity)).2
  change (bUpper N D L:ℚ) ≤ 2*mu N D/L+1 at hround
  have hceil := (upper_rounding (delta N D) (by unfold delta; positivity)).2
  have small : 2*mu N D/L ≤ mu N D/32768 := by
    apply (div_le_iff₀ hLpos).2
    have h := mul_le_mul_of_nonneg_left (show (65536:ℚ) ≤ L by linarith)
      (show 0≤mu N D/32768 by positivity)
    linarith
  have hPin : pinMeanUpper N D ≤ mu N D/16 := by
    unfold pinMeanUpper mu
    have hh : 0 ≤ (N:ℚ)/D := by positivity
    rw [mul_div_assoc (24:ℚ)]
    linarith
  have bsmall : (bUpper N D L:ℚ) ≤ mu N D/16384 := by linarith
  have oneSmall : (1:ℚ) ≤ mu N D / 131072 := by linarith
  unfold delta rho at *
  norm_num at *
  linarith

theorem sqrtMarkBudget_le_delta {N D L Δ E : ℕ}
    (hL : 2≤L) (hE : E≤24*N) (m : Margin N D L Δ) :
    Real.sqrt ((2*(E:ℝ)+9*(24*(N:ℝ)))/(L:ℝ)) ≤ (delta N D : ℝ) := by
  have hδ : (0:ℝ) ≤ (delta N D : ℝ) := by exact_mod_cast m.delta_nonneg
  have hmark : (24*(N:ℝ))*5^2 ≤ ((delta N D : ℚ) : ℝ)^2 := by exact_mod_cast m.mark
  have hp : (0:ℝ)<L := by exact_mod_cast (show 0<L by omega)
  have hLe : (2:ℝ)≤L := by exact_mod_cast hL
  have hEe : (E:ℝ)≤24*(N:ℝ) := by exact_mod_cast hE
  have ht : (2*(E:ℝ)+9*(24*(N:ℝ)))/(L:ℝ) ≤ (24*(N:ℝ))*5^2 := by
    apply (div_le_iff₀ hp).2
    have hh := mul_le_mul_of_nonneg_left hLe (show (0:ℝ)≤(24*(N:ℝ))*5^2 by positivity)
    linarith
  have hx : 0≤ (2*(E:ℝ)+9*(24*(N:ℝ)))/(L:ℝ) := by positivity
  have hy := Real.sq_sqrt hx
  have hnn := Real.sqrt_nonneg ((2*(E:ℝ)+9*(24*(N:ℝ)))/(L:ℝ))
  nlinarith [ht.trans hmark]

#print axioms enlargedMatchingMargin
#print axioms sqrtMarkBudget_le_delta
end Paper6JointSeating
