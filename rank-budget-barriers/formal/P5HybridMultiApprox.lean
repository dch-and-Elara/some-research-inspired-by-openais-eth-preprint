import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! Bridge the manuscript's arbitrary positive real weights and norm
into the existing rational matching kernel. No rationality of the
prescribed cuts or layout-domination constants is required. -/
namespace Paper5.HybridMulti
open scoped BigOperators Classical
open Real

variable {S : Type*} [Fintype S]

noncomputable def combinedScale (C w : S→ℝ) (k : S→ℕ) : ℝ :=
  ∑ s,w s*sqrt (C s*(k s:ℝ))

structure Approximation (C w : S→ℝ) (k : S→ℕ) where
  cq : S→ℚ
  wq : S→ℚ
  hq : S→ℚ
  dom : ∀ s,C s≤(cq s:ℝ)
  weights : ∀ s,w s/2≤(wq s:ℝ)
  norm : ∀ s,(wq s)^2*(cq s)*(k s:ℚ)≤(hq s)^2
  positive : ∀ s,0<hq s
  sum : (∑ s,(hq s:ℝ))≤3*combinedScale C w k

set_option maxHeartbeats 11500000 in
theorem exists_approximation (C w : S→ℝ) (k : S→ℕ)
    (hC : ∀ s,1≤C s) (hw : ∀ s,0<w s) (hk : ∀ s,0<k s) :
    Nonempty (Approximation C w k) := by
  let g (s : S) := w s*sqrt (C s*(k s:ℝ))
  have hg (s : S) : 0<g s := by
    have hcs : 0<C s := lt_of_lt_of_le (by norm_num) (hC s)
    have hks : 0<(k s:ℝ) := by exact_mod_cast hk s
    exact mul_pos (hw s) (sqrt_pos.mpr (mul_pos hcs hks))
  choose cq hcl hcu using fun s=>exists_rat_btwn (show C s<2*C s by linarith [hC s])
  choose wq hwl hwu using fun s=>exists_rat_btwn (show w s/2<w s by linarith [hw s])
  choose hq hhl hhu using fun s=>exists_rat_btwn (show 2*g s<3*g s by linarith [hg s])
  have hq0 (s : S) : 0<(hq s:ℝ) := (by linarith [hg s] : 0<2*g s).trans (hhl s)
  refine ⟨⟨cq,wq,hq,fun s=>(hcl s).le,fun s=>(hwl s).le,?_,?_,?_⟩⟩
  · intro s
    have hcs : 0<C s := lt_of_lt_of_le (by norm_num) (hC s)
    have hks : 0<(k s:ℝ) := by exact_mod_cast hk s
    have he : (g s)^2=(w s)^2*C s*(k s:ℝ) := by
      unfold g
      rw [mul_pow,sq_sqrt (by positivity)]
      ring
    have hqw : 0<(wq s:ℝ) := (by linarith [hw s] : 0<w s/2).trans (hwl s)
    have hNorm : (wq s:ℝ)^2*(cq s:ℝ)*(k s:ℝ)≤(hq s:ℝ)^2 := by
      calc
        _ ≤ (w s)^2*(2*C s)*(k s:ℝ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (pow_le_pow_left₀ hqw.le (hwu s).le 2) (hcu s).le
              (by linarith [hcl s,hcs]) (sq_nonneg _)) hks.le
        _ = 2*(g s)^2 := by rw [he]; ring
        _ ≤ (2*g s)^2 := by nlinarith only [sq_nonneg (g s)]
        _ ≤ _ := pow_le_pow_left₀ (by linarith [hg s]) (hhl s).le 2
    exact_mod_cast hNorm
  · intro s; exact_mod_cast hq0 s
  · unfold combinedScale
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun s _=>(hhu s).le)

theorem combinedScale_positive [Nonempty S] (C w : S→ℝ) (k : S→ℕ)
    (hC : ∀ s,1≤C s) (hw : ∀ s,0<w s) (hk : ∀ s,0<k s) :
    0<combinedScale C w k := by
  unfold combinedScale
  have hs (s : S) : 0<w s*sqrt (C s*(k s:ℝ)) := by
    have hc : 0<C s := lt_of_lt_of_le (by norm_num) (hC s)
    have hd : 0<(k s:ℝ) := by exact_mod_cast hk s
    exact mul_pos (hw s) (sqrt_pos.mpr (mul_pos hc hd))
  exact (hs (Classical.choice inferInstance)).trans_le
    (Finset.single_le_sum (fun s _=>(hs s).le) (Finset.mem_univ _))

theorem compare_rounded_margin (K N H h w v : ℝ)
    (hK : 0<K) (hN : 0<N) (hH : 0<H) (hh : 0<h) (hv : 0<v)
    (hw : w/2≤v) (hScale : h≤3*H) :
    K*N*w/(6*H)≤K*N*v/h := by
  calc
    _ = K*N*(w/2)/(3*H) := by ring
    _ ≤ K*N*v/(3*H) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw (by positivity)) (by positivity)
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hh hScale

#print axioms exists_approximation
#print axioms combinedScale_positive
#print axioms compare_rounded_margin
end Paper5.HybridMulti
