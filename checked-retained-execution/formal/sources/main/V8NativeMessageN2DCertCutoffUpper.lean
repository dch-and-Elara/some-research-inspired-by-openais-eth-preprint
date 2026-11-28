import V8NativeMessageN2DCertEta

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 17000000

/-! The last numeric step of v8 line 2242. The true rounded cutoff is
strictly below every root child satisfying the original certified lower
margin, since the root uses 24N wires and the exact four-copy size. -/
namespace V8NativeMessage.N2DCert
open Real Filter Paper5.HybridClosure.Printed J1PPrinted J9PrintedSchedule
open scoped Topology

noncomputable section

theorem d_size_tends_atTop : Tendsto dSize atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop n] with N hN
  exact hN.trans (d_size_bounds N).1

theorem d_lambda_tends_atTop : Tendsto dLambda atTop atTop := by
  have h : Tendsto (Nat.clog 2) atTop atTop := by
    simpa only [one_mul,add_zero] using clog_linear_tendsto 1 0 (by decide)
  exact h.comp d_size_tends_atTop

theorem d_root_cutoff_eventually_quarter :
    ∀ᶠ N : ℕ in atTop,4*nativeH (dSize N)≤N := by
  filter_upwards [eventually_ge_atTop (8:ℕ),
    d_lambda_tends_atTop.eventually (eventually_ge_atTop (88^2:ℕ))] with N hN hLarge
  let s := dSize N
  let d := (dLambda N).sqrt
  let H := nativeH s
  have hd : 88≤d := Nat.le_sqrt'.2 hLarge
  have hRound : H*d≤s+d-1 := Nat.div_mul_le_self _ _
  have hSub : (H-1)*d≤s := by
    rw [Nat.sub_mul,one_mul]
    omega
  have hSmall : 88*(H-1)≤11*N :=
    (Nat.mul_le_mul_right (H-1) hd).trans ((by
      simpa only [Nat.mul_comm] using hSub :
      d*(H-1)≤s).trans (d_size_bounds N).2)
  change 4*H≤N
  omega

theorem eta_on_cloned_size_eventually_below_half :
    ∀ᶠ N : ℕ in atTop,eta (dSize N)<1/2 :=
  (eta_printed_tends_to_zero.comp d_size_tends_atTop).eventually
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1/2))

theorem certified_root_margin_eventually_implies_active :
    ∀ᶠ N : ℕ in atTop,∀ m : ℕ,
      (1-eta (dSize N))*((24*N:ℕ):ℝ)/32≤(m:ℝ) → nativeH (dSize N)<m := by
  filter_upwards [eventually_ge_atTop (1:ℕ),d_root_cutoff_eventually_quarter,
    eta_on_cloned_size_eventually_below_half] with N hN hH he
  intro m hm
  have hNr : (0:ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have hHr : 4*(nativeH (dSize N):ℝ)≤(N:ℝ) := by exact_mod_cast hH
  have hr : (3:ℝ)*(N:ℝ)/8≤(m:ℝ) := by
    have h := mul_le_mul_of_nonneg_right (show (1/2:ℝ)≤1-eta (dSize N) by linarith only [he])
      hNr.le
    push_cast at hm
    nlinarith only [h,hm]
  have hFinal : (nativeH (dSize N):ℝ)<(m:ℝ) := by linarith only [hHr,hr,hNr]
  exact_mod_cast hFinal

#print axioms d_size_tends_atTop
#print axioms d_lambda_tends_atTop
#print axioms d_root_cutoff_eventually_quarter
#print axioms eta_on_cloned_size_eventually_below_half
#print axioms certified_root_margin_eventually_implies_active
end
end V8NativeMessage.N2DCert
