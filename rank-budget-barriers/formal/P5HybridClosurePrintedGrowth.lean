import P5HybridClosurePrintedMain
import P5HybridClosurePrintedD

/-! Printed parameter profiles satisfy the exact eventual finite tests
of the independent common-matching certificate, without replacing the
printed floors by asymptotic parameter choices. -/
namespace Paper5.HybridClosure.Printed
open scoped Topology
open Filter

noncomputable def printedLogConst : ℝ := 6/Real.log 2

theorem printed_log_const_pos : 0<printedLogConst :=
  div_pos (by norm_num) (Real.log_pos (by norm_num))

theorem clog_real_log_bound (N s k : ℕ) (hN : 2≤N) (hs : 1≤s) (h : s≤N^k) :
    (Nat.clog 2 s:ℝ)≤((k+1:ℕ):ℝ)/Real.log 2*Real.log (N:ℝ) := by
  have hs' : (1:ℝ)≤s := by exact_mod_cast hs
  have hN' : (2:ℝ)≤N := by exact_mod_cast hN
  have hlog2 := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hlogN : Real.log 2 ≤ Real.log (N:ℝ) := Real.log_le_log (by norm_num) hN'
  have hdiv : (1:ℝ)≤Real.log (N:ℝ)/Real.log 2 := (le_div_iff₀ hlog2).mpr (by simpa using hlogN)
  have hlog : Real.log (s:ℝ)≤(k:ℝ)*Real.log (N:ℝ) := by
    rw [←Real.log_pow]
    apply Real.log_le_log (zero_lt_one.trans_le hs')
    exact_mod_cast h
  calc
    (Nat.clog 2 s:ℝ) ≤ Real.log (s:ℝ)/Real.log 2 + 1 := by
      rw [←Real.natCeil_logb_natCast 2 s]
      exact (Nat.ceil_lt_add_one (Real.logb_nonneg (by norm_num) hs')).le
    _ ≤ (k:ℝ)*(Real.log (N:ℝ)/Real.log 2)+1 := by
      apply add_le_add_right
      rw [←mul_div_assoc]
      exact div_le_div_of_nonneg_right hlog hlog2.le
    _ ≤ _ := by
      have hc : ((k+1:ℕ):ℝ)/Real.log 2*Real.log (N:ℝ) =
          (k:ℝ)*(Real.log (N:ℝ)/Real.log 2)+Real.log (N:ℝ)/Real.log 2 := by
        push_cast
        ring
      rw [hc]
      linarith only [hdiv]

theorem printed_logarithmic_widths (N : ℕ) (hN : 2≤N) :
    (mainQ N:ℝ)≤printedLogConst*Real.log (N:ℝ) ∧
      (dU N:ℝ)≤printedLogConst*Real.log (N:ℝ) := by
  have hM : 4*N≤N^3 := by
    have hh : 4≤N^2 := Nat.pow_le_pow_left hN 2
    calc
      _ ≤ N^2*N := Nat.mul_le_mul_right _ hh
      _ = _ := (pow_succ _ _).symm
  have hD : dSize N≤N^5 := by
    refine (d_size_bounds N).2.trans ?_
    have hp : 11≤N^4 := (by decide : (11:ℕ)≤2^4).trans (Nat.pow_le_pow_left hN 4)
    exact (Nat.mul_le_mul_right _ hp).trans_eq (pow_succ _ _).symm
  have hlamM := clog_real_log_bound N (4*N) 3 hN (by omega) hM
  have hlamD := clog_real_log_bound N (dSize N) 5 hN (by have h := (d_size_bounds N).1; omega) hD
  have hd : dU N≤dLambda N := Nat.div_le_self _ _
  have hlogN : 0≤Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast (show 1≤N by omega))
  have hlog2 := Real.log_pos (by norm_num : (1:ℝ)<2)
  have hh : (4:ℝ)/Real.log 2*Real.log (N:ℝ)≤printedLogConst*Real.log (N:ℝ) := by
    unfold printedLogConst
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by norm_num) hlog2.le) hlogN
  constructor
  · have he : (mainQ N:ℝ)≤mainLambda N := by exact_mod_cast main_Q_le_lambda N
    exact he.trans ((by simpa [mainLambda] using hlamM :
      (mainLambda N:ℝ)≤(4:ℝ)/Real.log 2*Real.log (N:ℝ)).trans hh)
  · have he : (dU N:ℝ)≤dLambda N := by exact_mod_cast hd
    exact he.trans (by simpa [dLambda,printedLogConst] using hlamD)

structure Ready (gamma : ℚ) (N : ℕ) : Prop where
  mainAlphabet : 32≤mainR N
  mainNodes : 0<mainQ N
  mainLayout : 12*(mainCells N)^2≤4*N
  mainGroups : 2*mainQ N*(mainR N)^2≤4*N
  dActive : J9PrintedSchedule.leafThreshold (dSize N) (dLambda N)<24*N
  dNodes : 0<dU N
  dDegree : 3≤dDelta N
  dCollision : 2*(dCells N)^2*dDelta N≤24*N
  dSlot : dL N*dCells N≤24*N
  dPacketDegree : 2*dL N≤dDelta N
  unionBudget : 31104*((mainQ N:ℚ)^2+(dU N:ℚ)^2)<
    (matchingCoeff (gamma/3))^2*(N:ℚ)
  depth : (matchingCoeff (gamma/3):ℝ)/(4*Real.sqrt printedLogConst)*
      ((N:ℝ)/Real.sqrt (Real.log (N:ℝ))) ≤
    ((min (routeDepth (gamma/3) N (mainQ N)) (routeDepth (gamma/3) N (dU N)) : ℕ):ℝ)

theorem actual_printed_eventual_ready (gamma : ℚ) (hg : 0<gamma) :
    ∀ᶠ N : ℕ in atTop, Ready gamma N := by
  have hlog : ∀ᶠ N : ℕ in atTop,
      (mainQ N:ℝ)≤printedLogConst*Real.log (N:ℝ) ∧
        (dU N:ℝ)≤printedLogConst*Real.log (N:ℝ) := by
    filter_upwards [eventually_ge_atTop (2:ℕ)] with N hN
    exact printed_logarithmic_widths N hN
  have hg' : 0<gamma/3 := by positivity
  have hc : 0<(matchingCoeff (gamma/3):ℝ) := by exact_mod_cast matchingCoeff_pos _ hg'
  have hUnion := log_scale_gives_eventual_union mainQ dU printedLogConst
    (matchingCoeff (gamma/3):ℝ) hc hlog
  have hpos : ∀ᶠ N : ℕ in atTop, 0<mainQ N ∧ 0<dU N ∧
      (mainQ N:ℝ)≤printedLogConst*Real.log (N:ℝ) ∧
        (dU N:ℝ)≤printedLogConst*Real.log (N:ℝ) := by
    filter_upwards [main_printed_eventual,d_printed_eventual,hlog] with N hM hD hLog
    exact ⟨hM.2.1,hD.2.1,hLog⟩
  have hOmega := log_schedules_bigOmega_depth mainQ dU (gamma/3) hg' printedLogConst
    printed_log_const_pos hpos
  filter_upwards [main_printed_eventual,d_printed_eventual,hUnion,hOmega] with N hM hD hU hDepth
  exact ⟨hM.1,hM.2.1,hM.2.2.1,hM.2.2.2,hD.1,hD.2.1,hD.2.2.1,hD.2.2.2.1,
    hD.2.2.2.2.1,hD.2.2.2.2.2,by exact_mod_cast hU,hDepth⟩

#print axioms clog_real_log_bound
#print axioms printed_logarithmic_widths
#print axioms actual_printed_eventual_ready
end Paper5.HybridClosure.Printed