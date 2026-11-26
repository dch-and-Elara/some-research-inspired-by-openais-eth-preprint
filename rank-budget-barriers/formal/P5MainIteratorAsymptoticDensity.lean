import P5MainIteratorMarkov
import P5MainIteratorChoose
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Eventual density threshold in §6, uniformly over the actual
incidence count M and the selected label width Q. -/
namespace P5MainIterator
open scoped BigOperators Classical
open Real Filter

noncomputable def decayBase : ℝ := markBase*(3/4:ℝ)

theorem decayBase_pos : 0<decayBase := by unfold decayBase markBase; positivity
theorem decayBase_lt_one : decayBase<1 := badExponent_decay

noncomputable def excessCoeff (B : ℝ) :=
  B+log 4+B*|log (log 2)|+1

noncomputable def nativeCutoff (B : ℝ) :=
  256 + excessCoeff B / (-log decayBase)

theorem nativeCutoff_ge (B : ℝ) (hB : 0≤B) : 256≤nativeCutoff B := by
  have hb : 0 < -log decayBase := neg_pos.mpr (log_neg decayBase_pos decayBase_lt_one)
  unfold nativeCutoff excessCoeff
  have h : 0≤(B+log 4+B*|log (log 2)|+1)/(-log decayBase) := by
    apply div_nonneg _ hb.le
    have h4 : 0≤log 4 := log_nonneg (by norm_num)
    positivity
  linarith only [h]

theorem log_poly_incidence (x m B : ℝ) (hx : 1<x) (hm : 0<m)
    (hM : m≤x*(logTwo x)^B) :
    log m≤log x + B*(log (log x)-log (log 2)) := by
  have hx' : 0<x := by linarith only [hx]
  have hlx : 0<log x := log_pos hx
  have hl2 : 0<log 2 := log_pos (by norm_num)
  have hpow : 0<(logTwo x)^B := rpow_pos_of_pos (by unfold logTwo; positivity) _
  have H := log_le_log hm hM
  rw [log_mul hx'.ne' hpow.ne',log_rpow (show 0<logTwo x by unfold logTwo; positivity)] at H
  unfold logTwo at H
  rw [log_div hlx.ne' hl2.ne'] at H
  linarith only [H]

theorem log_le_twice_sqrt (x : ℝ) (hx : 0<x) : log x≤2*sqrt x := by
  have h := log_le_sub_one_of_pos (sqrt_pos.2 hx)
  rw [log_sqrt hx.le] at h
  linarith only [h]

set_option maxHeartbeats 5100000 in
theorem eventual_density_margins (B : ℝ) (hB : 0≤B) :
    ∀ᶠ x : ℝ in atTop, ∀ m : ℝ, 0<m → m≤x*(logTwo x)^B →
      log (2*m)≤2*log x ∧
      ∀ Q : ℕ, nativeCutoff B * log (log x) < (Q:ℝ) →
        256≤Q ∧ 2*m*decayBase^Q≤x/2 := by
  let C := log 2+B*|log (log 2)|
  have hL := tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 (max ((8*B)^2) (4*C))))
  have hl := (tendsto_log_atTop.comp tendsto_log_atTop).eventually (eventually_ge_atTop (1:ℝ))
  filter_upwards [eventually_ge_atTop (2:ℝ),hL,hl] with x hx hL' hl'
  intro m hm hM
  let L := log x
  let l := log L
  have hLmax : max 1 (max ((8*B)^2) (4*C))≤L := hL'
  have hl1 : 1≤l := hl'
  have hLpos : 0<L := log_pos (by linarith only [hx])
  have hxpos : 0<x := by linarith only [hx]
  have hp := log_poly_incidence x m B (by linarith only [hx]) hm hM
  have hlS : l≤2*sqrt L := log_le_twice_sqrt L hLpos
  have hS : 8*B≤sqrt L := by
    have hh := sqrt_le_sqrt ((le_max_left ((8*B)^2) (4*C)).trans ((le_max_right _ _).trans hLmax))
    simpa only [sqrt_sq (by positivity : 0≤8*B)] using hh
  have hSmall : B*l≤L/4 := by
    have h₁ := mul_le_mul_of_nonneg_left hlS hB
    have h₂ := mul_le_mul_of_nonneg_right hS (sqrt_nonneg L)
    nlinarith only [h₁,h₂,sq_sqrt hLpos.le]
  have hC : C≤L/4 := by
    linarith only [(le_max_right ((8*B)^2) (4*C)).trans ((le_max_right _ _).trans hLmax)]
  have hOther := mul_le_mul_of_nonneg_left (neg_abs_le (log (log 2))) hB
  constructor
  · rw [log_mul (by norm_num) hm.ne']
    dsimp [C] at hC
    linarith only [hp,hC,hSmall,hOther,hLpos]
  · intro Q hQ
    have hcut := nativeCutoff_ge B hB
    have hq' : 256≤(Q:ℝ) := by
      calc
        _ ≤ nativeCutoff B := hcut
        _ ≤ nativeCutoff B*l := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hl1 (by linarith only [hcut])
        _ ≤ _ := hQ.le
    refine ⟨by exact_mod_cast hq',?_⟩
    have hneg : 0 < -log decayBase := neg_pos.mpr (log_neg decayBase_pos decayBase_lt_one)
    have hCdef : excessCoeff B ≤ nativeCutoff B * (-log decayBase) := by
      unfold nativeCutoff
      rw [add_mul,div_mul_cancel₀ _ hneg.ne']
      linarith only [hneg]
    have hmain : (excessCoeff B)*l ≤ (Q:ℝ)*(-log decayBase) := by
      calc
        _ ≤ (nativeCutoff B*(-log decayBase))*l :=
          mul_le_mul_of_nonneg_right hCdef (by linarith only [hl1])
        _ = (nativeCutoff B*l)*(-log decayBase) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hQ.le hneg.le
    have h4 : log 4=2*log 2 := by rw [show (4:ℝ)=2^2 by norm_num,log_pow]; norm_num
    have hdens : 2*log 2+B*(l-log (log 2))≤excessCoeff B*l := by
      have hA : 0≤log 4+B*|log (log 2)| := by
        have h4' := log_nonneg (show (1:ℝ)≤4 by norm_num)
        positivity
      have ho := mul_le_mul_of_nonneg_left hl1 hA
      unfold excessCoeff
      rw [h4] at ho ⊢
      nlinarith only [ho,hOther,hl1]
    have hp2 : 0<2*m := by positivity
    have hpow := pow_pos decayBase_pos Q
    apply (log_le_log_iff (mul_pos hp2 hpow) (by positivity)).mp
    rw [log_mul hp2.ne' hpow.ne',log_mul (by norm_num) hm.ne',
        log_pow,log_div hxpos.ne' (by norm_num)]
    linarith only [hp,hdens,hmain]

#print axioms decayBase_pos
#print axioms nativeCutoff_ge
#print axioms log_poly_incidence
#print axioms eventual_density_margins
end P5MainIterator
