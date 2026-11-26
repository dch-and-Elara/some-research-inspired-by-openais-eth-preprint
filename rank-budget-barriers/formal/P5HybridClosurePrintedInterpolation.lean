import P5HybridClosurePrintedMain

/-! Extra MAIN numeric tuning used to identify the printed coordinates:
the bounded-occurrence multiplicity is exactly R=4 ceil(sqrt(lambda)).
This is not a new Taylor correctness claim. -/
namespace Paper5.HybridClosure.Printed
open scoped Topology
open Filter

noncomputable def mainMultiplicity (N : ℕ) : ℕ :=
  4*⌈Real.sqrt (mainLambda N:ℝ)⌉₊

theorem main_multiplicity_fit (N : ℕ) (hNu : 192≤mainNu N) :
    32≤mainMultiplicity N ∧ 6*mainMultiplicity N≤mainQ N := by
  let lam := mainLambda N
  let n := mainNu N
  let s := lam.sqrt
  let m := ⌈Real.sqrt (lam:ℝ)⌉₊
  have hn : 192≤n := hNu
  have hR := (main_printed_feasible N (by omega)).1
  have hs : 32*n^2≤s :=
    (Nat.mul_le_mul_right (n^2) hR).trans (Nat.div_mul_le_self _ _)
  have hScale : 6144*n≤s := by
    calc
      _ ≤ (32*n)*n := Nat.mul_le_mul_right n (by omega)
      _ = _ := by ring
      _ ≤ _ := hs
  have hm : m≤s+1 := Nat.ceil_le.mpr (by
    rw [Nat.cast_add,Nat.cast_one]
    exact (real_sqrt_lt_succ_nat lam).le)
  have hs_m : s≤m := by
    apply (Nat.cast_le (α:=ℝ)).mp
    exact (sqrt_nat_le_real lam).trans (Nat.le_ceil _)
  have hM : 8≤m := by omega
  have hM' : 32≤4*m := by omega
  have h_npos : 0<128*n := by positivity
  have hScale₂ : 0<s := by omega
  have hmul : (6*(4*m))*(128*n)≤lam := by
    calc
      _ = (3072*n)*m := by ring
      _ ≤ (3072*n)*(2*s) := Nat.mul_le_mul_left _ (by omega)
      _ = (6144*n)*s := by ring
      _ ≤ s*s := Nat.mul_le_mul_right _ hScale
      _ ≤ _ := Nat.sqrt_le lam
  exact ⟨hM',(Nat.le_div_iff_mul_le h_npos).mpr hmul⟩

theorem main_interpolation_tuning_eventual :
    ∀ᶠ N : ℕ in atTop, 32≤mainMultiplicity N ∧ 6*mainMultiplicity N≤mainQ N := by
  have hl : Tendsto mainLambda atTop atTop := by
    simpa [mainLambda] using clog_linear_tendsto 4 0 (by decide)
  have hn : Tendsto mainNu atTop atTop := by
    have h := (clog_linear_tendsto 1 0 (by decide)).comp hl
    simpa [mainNu,Function.comp_def] using h
  filter_upwards [hn.eventually (eventually_ge_atTop 192)] with N hN
  exact main_multiplicity_fit N hN

#print axioms main_multiplicity_fit
#print axioms main_interpolation_tuning_eventual
end Paper5.HybridClosure.Printed