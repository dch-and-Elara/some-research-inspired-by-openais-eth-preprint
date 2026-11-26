import P5MainBalanceSize
import P5MainBalanceHighOrder

/-! Make the exponent comparison in M.6 explicit, including integer
rounding at d/2. The only remaining size premise is a count of retained
coefficient addresses, not a rank or high-order premise. -/
namespace P5MainBalance
open scoped BigOperators Classical
open Real

noncomputable def exponentConstant (γ : ℚ) (C : ℕ) : ℝ :=
  (FiniteGrowth.coefficient γ (1/4):ℝ)/(4*sqrt (C:ℝ))

theorem exponentConstant_pos (γ : ℚ) (C : ℕ) (hγ : 0<γ) (hC : 0<C) :
    0<exponentConstant γ C := by
  have hv : 0<(FiniteGrowth.coefficient γ (1/4):ℝ) :=
    by exact_mod_cast FiniteGrowth.coefficient_pos hγ (by norm_num : (0:ℚ)<1/4)
  have hc : 0<(C:ℝ) := by exact_mod_cast hC
  exact div_pos hv (by positivity)

theorem unsquare_printed_exponent (γ : ℚ) (C Q N d : ℕ) (hγ : 0<γ)
    (hC : 0<C) (hQ : 0<Q)
    (h : (FiniteGrowth.coefficient γ (1/4)*N)^2≤16*(C:ℚ)*(Q:ℚ)*(d:ℚ)^2) :
    exponentConstant γ C*(N:ℝ)/sqrt (Q:ℝ)≤(d:ℝ) := by
  have hc : 0<(C:ℝ) := by exact_mod_cast hC
  have hq : 0<(Q:ℝ) := by exact_mod_cast hQ
  have hg : 0<(FiniteGrowth.coefficient γ (1/4):ℝ) :=
    by exact_mod_cast FiniteGrowth.coefficient_pos hγ (by norm_num : (0:ℚ)<1/4)
  let g := (FiniteGrowth.coefficient γ (1/4):ℝ)
  have H : (g*(N:ℝ))^2≤16*(C:ℝ)*(Q:ℝ)*(d:ℝ)^2 := by dsimp [g]; exact_mod_cast h
  have hs : (g*(N:ℝ))^2≤(4*sqrt (C:ℝ)*sqrt (Q:ℝ)*(d:ℝ))^2 := by
    calc
      _ ≤ _ := H
      _ = _ := by
        repeat' rw [mul_pow]
        rw [sq_sqrt hc.le,sq_sqrt hq.le]
        norm_num
  have hlinear : g*(N:ℝ)≤4*sqrt (C:ℝ)*sqrt (Q:ℝ)*(d:ℝ) := by
    by_contra! hn
    exact (not_lt_of_ge hs) (pow_lt_pow_left₀ hn (by positivity) (by decide : (2:ℕ)≠0))
  unfold exponentConstant
  apply (div_le_iff₀ (sqrt_pos.2 hq)).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (by positivity)).mpr
  linarith only [hlinear]

theorem native_high_order_exponent_room (γ : ℚ) (C Q N d indexCount : ℕ) (ε : ℝ)
    (hγ : 0<γ) (hC : 0<C) (hQ : 0<Q) (hε : 0≤ε)
    (h : (FiniteGrowth.coefficient γ (1/4)*N)^2≤16*(C:ℚ)*(Q:ℚ)*(d:ℚ)^2)
    (hmin : 2≤exponentConstant γ C*(N:ℝ)/sqrt (Q:ℝ))
    (he : 9*ε≤exponentConstant γ C*log 2)
    (hIndex : (indexCount:ℝ)<exp (ε*(N:ℝ)/sqrt (Q:ℝ))) :
    3*ε*(N:ℝ)/sqrt (Q:ℝ)≤((d/2:ℕ):ℝ)*log 2 ∧
      indexCount < 2^(d-d/2) := by
  have hd := unsquare_printed_exponent γ C Q N d hγ hC hQ h
  have hd2 : 2≤d := by exact_mod_cast hmin.trans hd
  have hQ' : 0<(Q:ℝ) := by exact_mod_cast hQ
  have hlog2 : 0<log 2 := log_pos (by norm_num)
  have hdiv : d≤3*(d/2) := by omega
  have hdiv' : (d:ℝ)≤3*((d/2:ℕ):ℝ) := by exact_mod_cast hdiv
  have h₁ : 9*ε*((N:ℝ)/sqrt (Q:ℝ))≤(exponentConstant γ C*log 2)*((N:ℝ)/sqrt (Q:ℝ)) :=
    mul_le_mul_of_nonneg_right he (by positivity)
  have h₂ := mul_le_mul_of_nonneg_right (hd.trans hdiv') hlog2.le
  have hGap : 3*ε*(N:ℝ)/sqrt (Q:ℝ)≤((d/2:ℕ):ℝ)*log 2 := by
    let X := (N:ℝ)/sqrt (Q:ℝ)
    have h₃ : 9*ε*X≤(exponentConstant γ C*X)*log 2 := by
      calc
        _ ≤ (exponentConstant γ C*log 2)*X := h₁
        _ = _ := by ring
    have h₄ : (exponentConstant γ C*X)*log 2≤3*((d/2:ℕ):ℝ)*log 2 := by
      calc
        _ = ((exponentConstant γ C*(N:ℝ))/sqrt (Q:ℝ))*log 2 := by dsimp [X]; ring
        _ ≤ _ := h₂
    have h₅ : 3*ε*X≤((d/2:ℕ):ℝ)*log 2 := by linarith only [h₃,h₄]
    exact (show 3*ε*(N:ℝ)/sqrt (Q:ℝ)=3*ε*X by dsimp [X]; ring).le.trans h₅
  refine ⟨hGap,?_⟩
  have hg' : ε*(N:ℝ)/sqrt (Q:ℝ)≤3*ε*(N:ℝ)/sqrt (Q:ℝ) := by
    apply div_le_div_of_nonneg_right _ (sqrt_nonneg _)
    nlinarith only [mul_nonneg hε (show 0≤(N:ℝ) by positivity)]
  have hdHalf : ((d/2:ℕ):ℝ)≤((d-d/2:ℕ):ℝ) := by exact_mod_cast (show d/2≤d-d/2 by omega)
  have hf : ε*(N:ℝ)/sqrt (Q:ℝ)≤((d-d/2:ℕ):ℝ)*log 2 :=
    hg'.trans (hGap.trans (mul_le_mul_of_nonneg_right hdHalf hlog2.le))
  have hE := exp_le_exp.mpr hf
  rw [exp_nat_mul,exp_log (by norm_num : (0:ℝ)<2)] at hE
  exact_mod_cast hIndex.trans_le hE

#print axioms exponentConstant_pos
#print axioms unsquare_printed_exponent
#print axioms native_high_order_exponent_room
end P5MainBalance
