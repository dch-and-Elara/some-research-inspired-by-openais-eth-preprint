import V8NativeMessageN5AsymptoticSchedule

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4500000

/-! The printed parameter budget absorbs the polynomial delivery
width and printed jet order in both of v8's original scales. -/
namespace V8NativeMessage.N5
open scoped BigOperators Topology
open Filter Paper5.HybridClosure Paper5.HybridClosure.Printed
noncomputable section

theorem printed_half_budget (N e : ℕ) (c a : ℝ)
    (hN : 1≤N) (hL : 1≤Real.log (N:ℝ)) (hr : 1≤mainR N)
    (small : 4*((e:ℝ)+1)*(mainLambda N:ℝ)^2≤c*(N:ℝ))
    (large : c*(N:ℝ)/Real.sqrt (mainLambda N:ℝ)≤a) :
    2*(Real.logb 2 ((12*N+1:ℕ):ℝ)+((mainR N:ℝ)+1)*(e*Real.logb 2 (N+1)))≤a := by
  let lam : ℝ := mainLambda N
  let S := Real.sqrt lam
  let r : ℝ := (mainR N:ℝ)+1
  let v : ℝ := (mainNu N:ℝ)^2
  have lamp : 1≤lam := hL.trans (printed_lambda_lower N hN)
  have lamn : 0≤lam := zero_le_one.trans lamp
  have sSq : S^2=lam := Real.sq_sqrt lamn
  have sOne : 1≤S := by
    rw [←Real.sqrt_one]
    exact Real.sqrt_le_sqrt lamp
  have sPos : 0<S := zero_lt_one.trans_le sOne
  have hNu := printed_nu_pos N hr
  have hn' : (1:ℝ)≤mainNu N := by exact_mod_cast hNu
  have hv1 : 1≤v := by
    unfold v
    nlinarith only [mul_nonneg (by positivity : (0:ℝ)≤mainNu N) (sub_nonneg.mpr hn'),hn']
  have hv : 0<v := zero_lt_one.trans_le hv1
  have rBound : r≤2*S := by
    apply (printed_groups_plus_one N hr hNu).trans
    apply (div_le_iff₀ hv).2
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hv1 (by positivity : (0:ℝ)≤2*S)
  obtain ⟨hK,hW₀⟩ := printed_output_log_ceilings N hN
  have hW : Real.logb 2 ((N:ℝ)+1)≤lam := by
    simpa only [Nat.cast_add,Nat.cast_one] using hW₀
  have hWp : 0≤Real.logb 2 ((N:ℝ)+1) := Real.logb_nonneg (by norm_num) (by linarith only [show (0:ℝ)≤N by positivity])
  have hrp : 0≤r := by dsimp [r]; positivity
  have hwidth : r*((e:ℝ)*Real.logb 2 ((N:ℝ)+1))≤2*S*((e:ℝ)*lam) := by
    refine mul_le_mul rBound (mul_le_mul_of_nonneg_left hW (by positivity)) ?_ (by positivity)
    exact mul_nonneg (by positivity) hWp
  have hLbuf : 2*lam≤2*lam*S := by
    have h := mul_le_mul_of_nonneg_left sOne (by positivity : (0:ℝ)≤2*lam)
    simpa only [mul_one] using h
  calc
    _ ≤ 2*(2*lam+2*S*((e:ℝ)*lam)) := by
      exact mul_le_mul_of_nonneg_left (add_le_add hK hwidth) (by norm_num)
    _ ≤ 4*((e:ℝ)+1)*lam*S := by nlinarith only [hLbuf]
    _ ≤ c*(N:ℝ)/S := by
      apply (le_div_iff₀ sPos).2
      calc
        _ = 4*((e:ℝ)+1)*lam*S^2 := by ring
        _ = 4*((e:ℝ)+1)*lam^2 := by rw [sSq]; ring
        _ ≤ _ := small
    _ ≤ _ := large

theorem printed_asymptotic_scale (N e width T : ℕ) (c a : ℝ) (hc : 0<c)
    (hN : 1≤N) (hL : 1≤Real.log (N:ℝ)) (hr : 1≤mainR N) (hw : 0<width)
    (hwpoly : width≤(N+1)^e)
    (small : 4*((e:ℝ)+1)*(mainLambda N:ℝ)^2≤c*(N:ℝ))
    (large : c*(N:ℝ)/Real.sqrt (mainLambda N:ℝ)≤a)
    (work : (a-Real.logb 2 ((12*N+1:ℕ):ℝ))/(mainR N+1)-Real.logb 2 width≤Real.logb 2 T) :
    a*(Real.log (Real.log (N:ℝ)))^2/
      (4*Real.sqrt printedLogConst*Real.sqrt (Real.log (N:ℝ)))≤Real.logb 2 T := by
  have hNu := printed_nu_pos N hr
  have hLam : 0<mainLambda N := by
    have q := hL.trans (printed_lambda_lower N hN)
    exact Nat.cast_pos.mp (zero_lt_one.trans_le q)
  have ha : 0≤a := by
    refine le_trans (div_nonneg ?_ (Real.sqrt_nonneg _)) large
    exact mul_nonneg hc.le (by positivity)
  have hb := printed_half_budget N e c a hN hL hr small large
  have low := guarded_printed_scale a N e width (12*N+1) T hNu hr hLam hw ha hwpoly hb work
  have hNum := mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (Real.log_nonneg hL) (printed_nu_lower N hN hL) 2) ha
  have hpos : 0<4*Real.sqrt (mainLambda N:ℝ) :=
    mul_pos (by norm_num) (Real.sqrt_pos_of_pos (by exact_mod_cast hLam))
  have hDen : 4*Real.sqrt (mainLambda N:ℝ)≤4*Real.sqrt printedLogConst*Real.sqrt (Real.log (N:ℝ)) := by
    have hN2 : 2≤N := by
      by_contra! he
      have hOne : N=1 := by omega
      simp [hOne] at hL
      linarith only [hL]
    have hd := Real.sqrt_le_sqrt (printed_lambda_upper N hN2)
    rw [Real.sqrt_mul printed_log_const_pos.le] at hd
    exact (mul_le_mul_of_nonneg_left hd (by norm_num)).trans_eq (mul_assoc _ _ _).symm
  calc
    _ ≤ a*(Real.log (Real.log (N:ℝ)))^2/(4*Real.sqrt (mainLambda N:ℝ)) :=
      div_le_div_of_nonneg_left (mul_nonneg ha (sq_nonneg _)) hpos hDen
    _ ≤ a*(mainNu N:ℝ)^2/(4*Real.sqrt (mainLambda N:ℝ)) :=
      div_le_div_of_nonneg_right hNum hpos.le
    _ ≤ _ := low

theorem polynomial_coefficient_absorb (N e coeff W : ℕ) (hc : coeff≤N+1)
    (h : W≤coeff*(N+1)^e) : W≤(N+1)^(e+1) := by
  refine h.trans ?_
  rw [pow_succ,mul_comm ((N+1)^e)]
  exact Nat.mul_le_mul_right _ hc

theorem positive_width_of_paid_power {m κ W T p : ℕ} (hp : 0<p)
    (h : 2^m≤κ*(W*T)^p) : 0<W := by
  by_contra! hW
  have h0 : W=0 := by omega
  have hx := (pow_pos (by decide : (0:ℕ)<2) m).trans_le h
  simp [h0,zero_pow hp.ne'] at hx

#print axioms printed_half_budget
#print axioms printed_asymptotic_scale
#print axioms polynomial_coefficient_absorb
#print axioms positive_width_of_paid_power
end
end V8NativeMessage.N5