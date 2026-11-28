import P5MainBalanceM6SizeB
set_option warningAsError true
namespace P5Editorial
open P5MainBalance P5MainBalance.M6 P5MainIterator Real Filter

/-- Exact ambient measurement-box estimate, uniformly on the printed MAIN schedule.
Any reachable measurement alphabet contained in this box has no larger cardinality. -/
theorem eventual_printed_log_ambient_box (C : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ M N D h cB : ℕ,
      M ≤ C*N → h*D ≤ 2*M → D ≤ C*n →
      (cB:ℝ) ≤ (D:ℝ)/(mainLambda n:ℝ)^5 →
      log ((((2*D+1)^(mainAlphabet n*(h*cB)) : ℕ)) : ℝ) ≤
        ε*(N:ℝ)/sqrt (mainNodes n:ℝ) := by
  filter_upwards [eventually_ge_atTop (2:ℕ), printed_nodes_eventually_large 4,
    printed_small_measurement_error C ε hε,
    lambda_ge_along_sizes (log (2*(C:ℝ)+1)),
    lambda_ge_along_sizes (2:ℝ)] with n hn hQ hErr hLog hLam
  intro M N D h cB hM hSeed hD hRow
  have hQ2 : 0 < mainNodes n := by omega
  have hQlam : mainNodes n ≤ mainLambda n := Nat.div_le_self _ _
  have hLam1 : 1 ≤ mainLambda n := by exact_mod_cast (show (1:ℝ) ≤ (mainLambda n:ℝ) by linarith)
  have hNu : 1 ≤ mainNu n := by
    by_contra! hν
    have hν0 : mainNu n = 0 := by omega
    have hn0 : mainNodes n = 0 := by simp [mainNodes,hν0]
    omega
  exact literal_measurement_small M N (mainAlphabet n) (h*cB) D (mainLambda n) (mainNodes n) C
    ε (1/(mainLambda n:ℝ)^5) hLam1 hQlam hQ2 (printed_alphabet_le_sqrt n hNu) hM
    (copied_source_count _ _ _ _ _ _ (by positivity) hSeed (by simpa only [mul_one_div] using hRow))
    le_rfl (printed_log_box_small C n D (by omega) hD hLog) hErr
#print axioms eventual_printed_log_ambient_box
end P5Editorial
