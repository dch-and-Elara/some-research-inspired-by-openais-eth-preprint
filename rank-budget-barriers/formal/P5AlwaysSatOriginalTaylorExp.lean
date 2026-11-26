import P5AlwaysSatOriginalTaylorEventual
import P5MainBalanceExponentRoom

/-! Restate the checked squared density witness as the displayed
exponential in (M.5) and (M.6). This does not sum execution costs. -/
namespace Paper5.AlwaysSatOriginal.Physical.Taylor
open P5MainBalance P5MainIterator P5MainBalance.M6 Real
open scoped BigOperators Classical

noncomputable def rankExponent (γ : ℚ) (C : ℕ) : ℝ :=
  exponentConstant γ C*log 2/3

theorem rank_exponent_pos (γ : ℚ) (C : ℕ) (hγ : 0<γ) (hC : 0<C) :
    0<rankExponent γ C := by
  unfold rankExponent
  exact div_pos (mul_pos (exponentConstant_pos γ C hγ hC) (log_pos (by norm_num))) (by norm_num)

theorem real_cut_bound (γ : ℚ) (C Q N d K : ℕ) (hγ : 0<γ) (hC : 0<C)
    (hQ : 0<Q)
    (hd : (FiniteGrowth.coefficient γ (1/4)*N)^2≤16*(C:ℚ)*(Q:ℚ)*(d:ℚ)^2)
    (hK : 2^(d/2)<K) :
    exp (rankExponent γ C*(N:ℝ)/sqrt (Q:ℝ)) ≤ (K:ℝ) := by
  have he := unsquare_printed_exponent γ C Q N d hγ hC hQ hd
  have hL := log_pos (by norm_num : (1:ℝ)<2)
  have hh : rankExponent γ C*(N:ℝ)/sqrt (Q:ℝ)≤(d:ℝ)*log 2/3 := by
    calc
      _ = (exponentConstant γ C*(N:ℝ)/sqrt (Q:ℝ))*log 2/3 := by
        unfold rankExponent
        ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right he hL.le) (by norm_num)
  by_cases hh2 : 2≤d
  · have hdiv : d≤3*(d/2) := by omega
    have hdivR : (d:ℝ)≤3*((d/2:ℕ):ℝ) := by exact_mod_cast hdiv
    have hProd := mul_le_mul_of_nonneg_right hdivR hL.le
    have hLog : (d:ℝ)*log 2/3≤((d/2:ℕ):ℝ)*log 2 := by
      linarith only [hProd]
    apply (exp_le_exp.mpr (hh.trans hLog)).trans
    rw [exp_nat_mul,exp_log (by norm_num : (0:ℝ)<2)]
    exact_mod_cast hK.le
  · have hd1 : d≤1 := by omega
    have hProd := mul_le_mul_of_nonneg_right (show (d:ℝ)≤1 by exact_mod_cast hd1) hL.le
    have hLog : (d:ℝ)*log 2/3≤log 2 := by
      linarith only [hProd,hL]
    apply (exp_le_exp.mpr (hh.trans hLog)).trans
    rw [exp_log (by norm_num : (0:ℝ)<2)]
    have hz : d/2=0 := by omega
    rw [hz,pow_zero] at hK
    exact_mod_cast hK

section Source
variable {V X W F Copy : Type*}
  [Fintype V] [DecidableEq V] [Fintype X] [Fintype W] [Fintype F] [Fintype Copy]
variable {n C d ell : ℕ}
variable (L : SourceLayout X W F Copy (Fin (mainNodes n)) (Fin (mainAlphabet n)))
    (mark : V↪X) (P : SourceRecipe L mark)

noncomputable def jetCutCost (S : Fin (mainNodes n)→Finset (Fin (mainAlphabet n)))
    (u : JetIndex (fun _ : Fin (mainNodes n)=>printedOrder n d) × Fin ell) : ℕ :=
  cutLength (EmpiricalCutMoments.labelCut (MainIncidence.labels mark (realCell L)) id S u.1.1)
    (fun σ=>nativeCoeff (trimV ell
       (actualH L mark (nativeGrid n)
         (printedMix (printedStart n) (mainWidth 1 n)) P σ)) (nativeGrid n u.1.1) u.1.2 u.2)

theorem actual_exp_M5_M6 (γ : ℚ) (ε : ℝ) (hγ : 0<γ) (hC : 0<C)
    (h : PrintedWitness n C d ell γ ε L mark P) :
    ∃ S : Fin (mainNodes n)→Finset (Fin (mainAlphabet n)),
      (∀ t, (1/4:ℚ)*Fintype.card V≤
        ((min (EmpiricalCutMoments.labelCut (pinWord L mark) id S t).card
          (Fintype.card V-(EmpiricalCutMoments.labelCut (pinWord L mark) id S t).card) : ℕ) : ℚ)) ∧
      let η := min ε (rankExponent γ C)
      let e := exp (η*(Fintype.card V:ℝ)/sqrt (mainNodes n:ℝ))
      (e ≤ ((∑ u,jetCutCost (d:=d) (ell:=ell) L mark P S u : ℕ):ℝ)) ∧
      ∃ u : JetIndex (fun _ : Fin (mainNodes n)=>printedOrder n d) × Fin ell,
        e ≤ (jetCutCost L mark P S u:ℝ) ∧
        η*(Fintype.card V:ℝ)/(sqrt (mainNodes n:ℝ)*log (2*(mainNodes n:ℝ))) < (u.1.2.val:ℝ) := by
  obtain ⟨S,hBal,r,hr,u,hj,hRank⟩ := h
  have hQ : 0<mainNodes n := lt_of_le_of_lt (Nat.zero_le _) u.1.1.isLt
  rw [Fintype.card_fin] at hr hj
  have he := real_cut_bound γ C (mainNodes n) (Fintype.card V) r
    (jetCutCost L mark P S u) hγ hC hQ hr hRank
  let η := min ε (rankExponent γ C)
  let e := exp (η*(Fintype.card V:ℝ)/sqrt (mainNodes n:ℝ))
  change ∃ S, _ ∧ e≤_ ∧ ∃ u, e≤_ ∧ _
  have he' : e≤(jetCutCost L mark P S u:ℝ) := by
    apply le_trans (exp_le_exp.mpr ?_) he
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity))
      (sqrt_nonneg _)
  have hsum : jetCutCost L mark P S u≤∑ v,jetCutCost L mark P S v :=
    Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ u)
  refine ⟨S,hBal,he'.trans (by exact_mod_cast hsum),u,he',?_⟩
  have hden : 0≤sqrt (mainNodes n:ℝ)*log (2*(mainNodes n:ℝ)) := by
    have hq : (1:ℝ)≤(mainNodes n:ℝ) := by exact_mod_cast hQ
    exact mul_nonneg (sqrt_nonneg _) (log_nonneg (by linarith only [hq]))
  exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity))
    hden).trans_lt hj
end Source

#print axioms rank_exponent_pos
#print axioms real_cut_bound
#print axioms actual_exp_M5_M6
end Paper5.AlwaysSatOriginal.Physical.Taylor