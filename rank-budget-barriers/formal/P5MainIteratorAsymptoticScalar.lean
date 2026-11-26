import P5MainIteratorOptimize

/-! The finite scalar margins in F.A4 eventually hold with natural
logarithms. The proof uses only log u ≤ u-1 and explicit thresholds. -/
namespace P5MainIterator
open scoped BigOperators Classical
open Real Filter

structure ScaleMargins (x κ δ cutoff : ℝ) where
  Lpos : 0 < log x
  lpos : 0 < log (log x)
  alphaCost : 1 ≤ x * targetScale (log x) (log (log x))
  alphaOne : targetScale (log x) (log (log x)) ≤ 1
  cutoffSmall : targetScale (log x) (log (log x)) * cutoff * log (log x) ≤ κ/4
  widthSmall : targetScale (log x) (log (log x)) ≤ κ/64
  alphaDecay : targetScale (log x) (log (log x)) ≤ exp (-log (log x)/4)
  widthDecay : log (log x) / sqrt (log x) ≤ exp (-log (log x)/4)
  choiceLarge : 2 ≤ δ*x*log (log x)/sqrt (log x)
  threshold : log (log x)/4 ≤ log tailConstant - log (2*targetScale (log x) (log (log x)))

theorem log_le_sixteenth (x : ℝ) (hx : 1024≤x) : log x≤x/16 := by
  have hp : 0<x := by linarith only [hx]
  have hs := sqrt_le_sqrt hx
  norm_num at hs
  have ht := log_le_sub_one_of_pos (sqrt_pos.2 hp)
  rw [log_sqrt hp.le] at ht
  have h := mul_nonneg (sub_nonneg.mpr hs) (sqrt_nonneg x)
  nlinarith only [ht,h,sq_sqrt hp.le]

set_option maxHeartbeats 10500000 in
theorem eventual_scale_margins (κ δ cutoff : ℝ) (hκ : 0<κ) (hδ : 0<δ) (hc : 0<cutoff) :
    ∀ᶠ x : ℝ in atTop, Nonempty (ScaleMargins x κ δ cutoff) := by
  let A := |log tailConstant| + |log 2| + |log cutoff| + |log (κ/4)| + |log (κ/64)|+1
  have hL := tendsto_log_atTop.eventually (eventually_ge_atTop (max 1 ((2/δ)^2)))
  have hl := (tendsto_log_atTop.comp tendsto_log_atTop).eventually
    (eventually_ge_atTop (max 1024 (16*A)))
  filter_upwards [eventually_ge_atTop (1:ℝ),hL,hl] with x hx hL' hl'
  let L := log x
  let l := log L
  let α := targetScale L l
  have hLge : max 1 ((2/δ)^2)≤L := hL'
  have hlge : max 1024 (16*A)≤l := hl'
  have hL1 : 1≤L := (le_max_left _ _).trans hLge
  have hLpos : 0<L := by linarith only [hL1]
  have hlbig : 1024≤l := (le_max_left _ _).trans hlge
  have hl1 : 1≤l := by linarith only [hlbig]
  have hlpos : 0<l := by linarith only [hl1]
  have hαpos : 0<α := by dsimp [α,targetScale]; positivity
  have hconst : A≤l/16 := by linarith only [(le_max_right 1024 (16*A)).trans hlge]
  have ha₁ : -l/16≤log tailConstant := by
    dsimp [A] at hconst
    linarith only [hconst,neg_abs_le (log tailConstant),abs_nonneg (log 2),abs_nonneg (log cutoff),
      abs_nonneg (log (κ/4)),abs_nonneg (log (κ/64))]
  have ha₂ : log 2≤l/16 := by
    dsimp [A] at hconst
    linarith only [hconst,le_abs_self (log 2),abs_nonneg (log tailConstant),abs_nonneg (log cutoff),
      abs_nonneg (log (κ/4)),abs_nonneg (log (κ/64))]
  have ha₃ : log cutoff≤l/16 := by
    dsimp [A] at hconst
    linarith only [hconst,le_abs_self (log cutoff),abs_nonneg (log tailConstant),abs_nonneg (log 2),
      abs_nonneg (log (κ/4)),abs_nonneg (log (κ/64))]
  have ha₄ : -l/16≤log (κ/4) := by
    dsimp [A] at hconst
    linarith only [hconst,neg_abs_le (log (κ/4)),abs_nonneg (log tailConstant),abs_nonneg (log 2),
      abs_nonneg (log cutoff),abs_nonneg (log (κ/64))]
  have ha₅ : -l/16≤log (κ/64) := by
    dsimp [A] at hconst
    linarith only [hconst,neg_abs_le (log (κ/64)),abs_nonneg (log tailConstant),abs_nonneg (log 2),
      abs_nonneg (log cutoff),abs_nonneg (log (κ/4))]
  have hll := log_le_sixteenth l hlbig
  have hAlog : log α=2*log l-l/2 := by
    unfold α targetScale
    rw [log_div (by positivity) (by positivity),log_pow,log_sqrt hLpos.le]
    rfl
  have hAlow : log α≤-3*l/8 := by rw [hAlog]; linarith only [hll]
  have hαe : α≤exp (-l/4) := by
    apply (log_le_iff_le_exp hαpos).mp
    linarith only [hAlow,hlpos]
  have hwidth : l/sqrt L≤exp (-l/4) := by
    apply (log_le_iff_le_exp (by positivity)).mp
    rw [log_div hlpos.ne' (by positivity),log_sqrt hLpos.le]
    change log l-l/2≤-l/4
    linarith only [hll,hlpos]
  have hc' : α*cutoff*l≤κ/4 := by
    apply (log_le_log_iff (by positivity) (by positivity)).mp
    rw [log_mul (by positivity) hlpos.ne',log_mul hαpos.ne' hc.ne']
    linarith only [hAlow,ha₃,ha₄,hll,hlpos]
  have hκ' : α≤κ/64 := (log_le_log_iff hαpos (by positivity)).mp (by linarith only [hAlow,ha₅,hlpos])
  have hth : l/4≤log tailConstant-log (2*α) := by
    rw [log_mul (by norm_num) hαpos.ne']
    linarith only [hAlow,ha₁,ha₂]
  have hxP : 0<x := by linarith only [hx]
  have hxL : L≤x := by
    have ht := log_le_sub_one_of_pos hxP
    dsimp [L]
    linarith only [ht]
  have hratio : sqrt L ≤ x/sqrt L := by
    apply (le_div_iff₀ (sqrt_pos.2 hLpos)).mpr
    simpa only [←pow_two,sq_sqrt hLpos.le] using hxL
  have hS1 : 1≤sqrt L := by simpa using sqrt_le_sqrt hL1
  have hSδ : 2/δ≤sqrt L := by
    have H := sqrt_le_sqrt ((le_max_right 1 ((2/δ)^2)).trans hLge)
    simpa only [sqrt_sq (by positivity : 0≤2/δ)] using H
  have hαcost : 1≤x*α := by
    have h₁ : 1≤l^2 := by nlinarith only [hl1,sq_nonneg (l-1)]
    have h₂ : 1*1≤(x/sqrt L)*l^2 :=
      mul_le_mul (hS1.trans hratio) h₁ (by norm_num) (by positivity)
    calc
      (1:ℝ) = 1*1 := by norm_num
      _ ≤ (x/sqrt L)*l^2 := h₂
      _ = x*α := by dsimp [α,targetScale]; ring
  have hδlarge : 2≤δ*x*l/sqrt L := by
    have h₁ : 2≤δ*sqrt L := by rw [mul_comm]; exact (div_le_iff₀ hδ).mp hSδ
    calc
      _ ≤ δ*sqrt L := h₁
      _ ≤ δ*(x/sqrt L) := mul_le_mul_of_nonneg_left hratio hδ.le
      _ = (δ*(x/sqrt L))*1 := by ring
      _ ≤ (δ*(x/sqrt L))*l := mul_le_mul_of_nonneg_left hl1 (by positivity)
      _ = _ := by ring
  refine ⟨⟨hLpos,hlpos,hαcost,?_,hc',hκ',hαe,hwidth,hδlarge,hth⟩⟩
  exact hαe.trans (by rw [←exp_zero]; exact exp_le_exp.mpr (by linarith only [hlpos]))

#print axioms log_le_sixteenth
#print axioms eventual_scale_margins
end P5MainIterator
