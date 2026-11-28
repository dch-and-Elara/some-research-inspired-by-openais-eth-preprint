import P5MainBalanceSchedule
import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 12000000

/-! Exact conversion of the manuscript's printed rounded MAIN exponent
to its natural log/loglog scale. The graph has N vertices and the
denominator uses the actual source variable count n=4N. -/
namespace V8NativeMessage.N2PostBounds
open Real Filter P5MainBalance P5MainIterator
open scoped Topology

noncomputable section

def workScale (N : ℕ) : ℝ :=
  (N:ℝ)*(log (log (N:ℝ)))^2/sqrt (log (N:ℝ))

def wordMean (N : ℕ) : ℝ := ((4*N:ℕ):ℝ)/(mainAlphabet (4*N):ℝ)

def lambdaLogConstant : ℝ := 1/log 2+1

def cloneLogConstant : ℝ := 1+log 4

theorem lambdaLogConstant_ge_one : 1≤lambdaLogConstant := by
  unfold lambdaLogConstant
  have hh : 0≤(1:ℝ)/log 2 := one_div_nonneg.mpr (log_nonneg (by norm_num))
  linarith only [hh]

theorem cloneLogConstant_ge_one : 1≤cloneLogConstant := by
  unfold cloneLogConstant
  have hh : 0≤log (4:ℝ) := log_nonneg (by norm_num)
  linarith only [hh]

theorem lambda_le_literal_log (n : ℕ) (hlog : 1≤log (n:ℝ)) :
    (mainLambda n:ℝ)≤lambdaLogConstant*log (n:ℝ) := by
  have h2 := log_pos (by norm_num : (1:ℝ)<2)
  have hn : 0≤logTwo (n:ℝ) := div_nonneg (by linarith only [hlog]) h2.le
  have hp := Nat.ceil_lt_add_one hn
  change (mainLambda n:ℝ)<log (n:ℝ)/log 2+1 at hp
  unfold lambdaLogConstant
  rw [add_mul,one_mul,one_div_mul_eq_div]
  linarith only [hp,hlog]

theorem clone_input_log_bound (N : ℕ) (hN : 0<N) (hNL : 1≤log (N:ℝ)) :
    log ((4*N:ℕ):ℝ) ≤ cloneLogConstant*log (N:ℝ) := by
  have hN' : (0:ℝ)<N := by exact_mod_cast hN
  have h4 : 0≤log (4:ℝ) := log_nonneg (by norm_num)
  have hp := mul_le_mul_of_nonneg_left hNL h4
  rw [Nat.cast_mul,Nat.cast_ofNat,log_mul (by norm_num) hN'.ne']
  unfold cloneLogConstant
  nlinarith only [hp]

def mainCoeff : ℝ := 4/sqrt (lambdaLogConstant*cloneLogConstant)

theorem mainCoeff_pos : 0 < mainCoeff := by
  unfold mainCoeff
  have hL : 0 < lambdaLogConstant := zero_lt_one.trans_le lambdaLogConstant_ge_one
  have hC : 0 < cloneLogConstant := zero_lt_one.trans_le cloneLogConstant_ge_one
  positivity

theorem log_two_le_one : Real.log 2≤1 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at h
  exact h

theorem log_le_mainLambda (n : ℕ) :
    log (n:ℝ)≤(mainLambda n:ℝ) := by
  have h := (div_le_iff₀ (log_pos (by norm_num : (1:ℝ)<2))).mp
    (Nat.le_ceil (logTwo (n:ℝ)))
  change log (n:ℝ)≤(mainLambda n:ℝ)*log 2 at h
  exact h.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left log_two_le_one
      (show 0≤(mainLambda n:ℝ) by positivity))

theorem log_le_mainNu (n : ℕ) :
    log (mainLambda n:ℝ)≤(mainNu n:ℝ) := by
  have h := (div_le_iff₀ (log_pos (by norm_num : (1:ℝ)<2))).mp
    (Nat.le_ceil (logTwo (mainLambda n:ℝ)))
  change log (mainLambda n:ℝ)≤(mainNu n:ℝ)*log 2 at h
  exact h.trans (by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left log_two_le_one
      (show 0≤(mainNu n:ℝ) by positivity))

theorem printed_mean_pointwise (N : ℕ) (hNL : 1≤log (N:ℝ))
    (hNN : 1≤log (log (N:ℝ))) (hR : 0 < mainAlphabet (4*N)) :
    mainCoeff*workScale N ≤ wordMean N := by
  let n := 4*N
  let lam : ℝ := mainLambda n
  let nu : ℝ := mainNu n
  let r : ℝ := mainAlphabet n
  let x : ℝ := log (N:ℝ)
  let y : ℝ := log x
  let C := lambdaLogConstant*cloneLogConstant
  have hN0 : 0 < N := by
    by_contra! h
    have hn : N=0 := by omega
    norm_num [hn] at hNL
  have hnN : N≤n := by dsimp [n]; omega
  have hx : 0 < x := zero_lt_one.trans_le hNL
  have hy : 0 < y := zero_lt_one.trans_le hNN
  have hNr : (N:ℝ)≤n := by exact_mod_cast hnN
  have hlogN : x≤log (n:ℝ) := log_le_log (by exact_mod_cast hN0) hNr
  have hlogn : 1≤log (n:ℝ) := hNL.trans hlogN
  have hXL : x≤lam := hlogN.trans (log_le_mainLambda n)
  have hYν : y≤nu := (log_le_log hx hXL).trans (log_le_mainNu n)
  have hν : 0 < nu := hy.trans_le hYν
  have hr : 0 < r := by
    change 0 < (mainAlphabet (4*N):ℝ)
    exact_mod_cast hR
  have hCL : 0 < lambdaLogConstant := zero_lt_one.trans_le lambdaLogConstant_ge_one
  have hCC : 0 < cloneLogConstant := zero_lt_one.trans_le cloneLogConstant_ge_one
  have hC : 0 < C := mul_pos hCL hCC
  have hLamUpper : lam≤C*x := by
    calc
      _ ≤ lambdaLogConstant*log (n:ℝ) := lambda_le_literal_log n hlogn
      _ ≤ lambdaLogConstant*(cloneLogConstant*x) :=
        mul_le_mul_of_nonneg_left (clone_input_log_bound N hN0 hNL) hCL.le
      _ = _ := by dsimp [C]; ring
  have hRU : r≤sqrt lam/nu^2 := by
    change (⌊sqrt (mainLambda n:ℝ)/(mainNu n:ℝ)^2⌋₊:ℝ)≤sqrt lam/nu^2
    exact Nat.floor_le (by positivity)
  have hR2 : r*nu^2≤sqrt lam :=
    (le_div_iff₀ (pow_pos hν _)).mp hRU
  have hRoot : sqrt lam≤sqrt C*sqrt x := (sqrt_le_sqrt hLamUpper).trans_eq (sqrt_mul hC.le _)
  have hProd : y^2*r≤sqrt C*sqrt x := by
    calc
      _ ≤ nu^2*r := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy.le hYν 2) hr.le
      _ ≤ sqrt lam := by simpa only [mul_comm] using hR2
      _ ≤ _ := hRoot
  calc
    _ = (4*(N:ℝ)*y^2)/(sqrt C*sqrt x) := by
      unfold mainCoeff workScale
      dsimp [C,x,y]
      ring
    _ ≤ (4*(N:ℝ))/r := by
      apply (div_le_div_iff₀ (mul_pos (sqrt_pos.mpr hC) (sqrt_pos.mpr hx)) hr).mpr
      calc
        _ = (4*(N:ℝ))*(y^2*r) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hProd (by positivity)
    _ = wordMean N := by simp [wordMean,r,n]

theorem along_four_clones {p : ℕ→Prop} (h : ∀ᶠ n : ℕ in atTop,p n) :
    ∀ᶠ N : ℕ in atTop,p (4*N) := by
  obtain ⟨K,hK⟩ := eventually_atTop.mp h
  exact eventually_atTop.mpr ⟨K,fun N hN=>hK (4*N) (by omega)⟩

theorem printed_mean_eventually :
    ∀ᶠ N : ℕ in atTop, 0 < mainAlphabet (4*N) ∧ mainCoeff*workScale N ≤ wordMean N := by
  have hLog : Tendsto (fun N : ℕ=>log (N:ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLogLog : Tendsto (fun N : ℕ=>log (log (N:ℝ))) atTop atTop :=
    tendsto_log_atTop.comp hLog
  filter_upwards [hLog.eventually (eventually_ge_atTop (1:ℝ)),
    hLogLog.eventually (eventually_ge_atTop (1:ℝ)),
    along_four_clones (printed_alphabet_eventually_large 1)] with N hL hLL hR
  exact ⟨hR,printed_mean_pointwise N hL hLL hR⟩

#print axioms lambda_le_literal_log
#print axioms clone_input_log_bound
#print axioms mainCoeff_pos
#print axioms log_two_le_one
#print axioms log_le_mainLambda
#print axioms log_le_mainNu
#print axioms printed_mean_pointwise
#print axioms along_four_clones
#print axioms printed_mean_eventually
end
end V8NativeMessage.N2PostBounds
