import P5MainBalanceM6SizeA

/-! All rounding and asymptotic inequalities required by M.6, uniformly
over layouts of the fixed-density printed family. The only row input
is the source's separate spectral tail count, not an upper bound for
the low-order representation. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator Real Filter
open scoped BigOperators Classical

noncomputable def sourceTail (n : ℕ) : ℝ :=
  2*exp (-(mainWidth 1 n:ℝ)^2/(8*(mainNodes n:ℝ)))

theorem copied_source_count (r h D cB M : ℕ) (δ : ℝ)
    (hδ : 0≤δ) (hCells : h*D≤2*M) (hRow : (cB:ℝ)≤(D:ℝ)*δ) :
    (r:ℝ)*((h*cB:ℕ):ℝ)≤2*(M:ℝ)*(r:ℝ)*δ := by
  have hC : (h:ℝ)*(D:ℝ)≤2*(M:ℝ) := by exact_mod_cast hCells
  calc
    _ ≤ (r:ℝ)*((h:ℝ)*((D:ℝ)*δ)) := by
      push_cast
      gcongr
    _ = ((h:ℝ)*(D:ℝ))*((r:ℝ)*δ) := by ring
    _ ≤ (2*(M:ℝ))*((r:ℝ)*δ) := mul_le_mul_of_nonneg_right hC (by positivity)
    _ = _ := by ring

theorem sourceTail_nonneg (n : ℕ) : 0≤sourceTail n := by unfold sourceTail; positivity

set_option maxHeartbeats 14000000 in
theorem eventual_numeric_M6 (a C p : ℕ) (ha : 0<a) (hC : 0<C)
    (γ : ℚ) (hγ : 0<γ) (ε : ℝ) (hε : 0<ε) (hεOne : ε≤1)
    (hεGap : 9*ε≤exponentConstant γ C*log 2) :
    ∀ᶠ n : ℕ in atTop, ∀ N M D h cB ell idx : ℕ,
      N≤n → n≤a*N → M≤C*N → h*D≤2*M → (cB:ℝ)≤(D:ℝ)*sourceTail n →
      ell≤n+1 → idx≤n^p →
      4≤mainNodes n ∧
      2*(a:ℝ)≤ε*sqrt (mainNodes n:ℝ) ∧
      (∀ j : ℕ,
        (j:ℝ)*log (2*(mainNodes n:ℝ))≤ε*(N:ℝ)/sqrt (mainNodes n:ℝ) →
        ((((2*M+1)^(mainAlphabet n*(h*cB)))*ell*(j+1):ℕ):ℝ)≤
          exp (ε*(N:ℝ)/sqrt (mainNodes n:ℝ))) ∧
      (∀ d : ℕ,
        (FiniteGrowth.coefficient γ (1/4)*N)^2≤16*(C:ℚ)*(mainNodes n:ℚ)*(d:ℚ)^2 →
        3*ε*(N:ℝ)/sqrt (mainNodes n:ℝ)≤((d/2:ℕ):ℝ)*log 2 ∧ idx<2^(d-d/2)) := by
  have hc := exponentConstant_pos γ C hγ hC
  filter_upwards [eventually_ge_atTop (2:ℕ),printed_nodes_eventually_large 4,
    printed_fast_condition a ε hε,printed_small_measurement_error C (ε/2) (by positivity),
    lambda_ge_along_sizes (log (2*(C:ℝ)+1)),
    printed_polynomial_overhead_small a 4 ha (ε/2) (by positivity),
    printed_polynomial_overhead_small a p ha ε hε,
    printed_exponent_eventually_ge_two a ha (exponentConstant γ C) hc] with
      n hn hQ hFast hErr hLog hPoly hIdx hMin
  intro N M D h cB ell idx hN hnN hM hCells hRow hEll hIdxSize
  have hQ2 : 0<mainNodes n := by omega
  have hQlam : mainNodes n≤mainLambda n := Nat.div_le_self _ _
  have hLa : 2≤mainLambda n := by omega
  have hNu : 1≤mainNu n := by
    by_contra! hν
    have hν0 : mainNu n=0 := by omega
    have hn0 : mainNodes n=0 := by simp [mainNodes,hν0]
    omega
  refine ⟨hQ,hFast,?_,?_⟩
  · intro j hj
    let Y : ℕ := (2*M+1)^(mainAlphabet n*(h*cB))
    have hY : 0<(Y:ℝ) := by dsimp [Y]; positivity
    have hYlog : log (Y:ℝ)≤(ε/2)*(N:ℝ)/sqrt (mainNodes n:ℝ) :=
      literal_measurement_small M N (mainAlphabet n) (h*cB) M (mainLambda n) (mainNodes n) C
        (ε/2) (sourceTail n) (by omega) hQlam hQ2 (printed_alphabet_le_sqrt n hNu) hM
        (copied_source_count _ _ _ _ _ _ (sourceTail_nonneg n) hCells hRow)
        (literal_small_tail_product n hLa hQ2)
        (printed_log_box_small C n M (by omega) (hM.trans (Nat.mul_le_mul_left _ hN)) hLog) hErr
    have hYexp := exp_le_exp.mpr hYlog
    rw [exp_log hY] at hYexp
    let A := (ε/2)*(N:ℝ)/sqrt (mainNodes n:ℝ)
    have hSmallNat := literal_local_poly_by_n n ell j N (mainNodes n) ε hn hN hQ hεOne hEll hj
    have hSmall : ((ell*(j+1):ℕ):ℝ)≤exp A :=
      (by exact_mod_cast hSmallNat : ((ell*(j+1):ℕ):ℝ)≤(n:ℝ)^4).trans
        (hPoly N hnN hQ2).le
    have hBoth := mul_le_mul hYexp hSmall (by positivity) (exp_nonneg _)
    change _≤exp A*exp A at hBoth
    rw [←exp_add] at hBoth
    convert hBoth using 1
    · push_cast
      unfold Y
      push_cast
      ring
    · congr 1
      unfold A
      ring
  · intro d hd
    exact native_high_order_exponent_room γ C (mainNodes n) N d idx ε hγ hC hQ2 hε.le hd
      (hMin N hnN hQ2) hεGap
      ((by exact_mod_cast hIdxSize : (idx:ℝ)≤(n:ℝ)^p).trans_lt (hIdx N hnN hQ2))

#print axioms copied_source_count
#print axioms eventual_numeric_M6
end P5MainBalance.M6
