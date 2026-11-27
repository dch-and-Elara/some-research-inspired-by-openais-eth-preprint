import Paper1LiteralPeriodCost
import Paper1LiteralCut
import BooleanCube.Symmetric
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The literal residue class and log-dependent central margin of the
printed upper bound, equations (11)–(13). -/

namespace LocalReconstruction.Paper1Coverage

open Filter Finset
open scoped Topology BigOperators
noncomputable section

private theorem dimension_atTop : Tendsto (fun q : ℕ => (q:ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop

private theorem log_cubed_over_dimension :
    Tendsto (fun q : ℕ => (Real.log q)^3/(q:ℝ)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (3:ℝ) (s := 1) (by norm_num)).tendsto_div_nhds_zero.comp
    dimension_atTop
  change Tendsto (fun q : ℕ => (Real.log q)^((3:ℕ):ℝ)/(q:ℝ)^(1:ℝ)) atTop (𝓝 0) at h
  simpa only [Real.rpow_natCast, Real.rpow_one] using h

private theorem log_double_weight_constant :
    Real.log 2 + Real.log (2/Real.pi)/2 = Real.log (8/Real.pi)/2 := by
  rw [Real.log_div (by norm_num) Real.pi_pos.ne', Real.log_div (by norm_num) Real.pi_pos.ne',
    show (8:ℝ) = 2^3 by norm_num, Real.log_pow]
  ring

/-- The exact rightmost central-pair bound in (12), for the actual printed
floor and the exact slack `1/(2 log q)`. Counts are multiplied by `2^q`. -/
theorem literal_central_pair_eq12 (γ : ℝ) (hγ : 1/2 < γ) :
    ∀ᶠ q : ℕ in atTop, 2*(q.choose (literalCut γ q):ℝ) ≤
      measurementBudget q γ * (1-1/(2*Real.log q)) := by
  obtain ⟨M,hM,hW⟩ := literal_gap_in_moderate_window γ hγ
  let A := 3+4*M^2+48*M^4
  have errLim := log_cubed_over_dimension.const_mul A
  rw [mul_zero] at errLim
  have err := errLim.eventually (Iio_mem_nhds (show (0:ℝ)<1/4 by norm_num))
  filter_upwards [literal_cut_rounding γ hγ, literal_gap_squared_lower γ hγ, hW,
    uniform_local_binomial M hM, err, symmetric_log_atTop.eventually_ge_atTop 2,
    dimension_atTop.eventually_gt_atTop 0] with q hcut hgap hw hu he hlog hq
  let l := literalCut γ q
  let L := Real.log q
  let B := measurementBudget q γ
  have hL2 : 2 ≤ L := hlog
  have hL : 0 < L := by linarith
  have hlq : l ≤ q := by dsimp [l]; omega
  have lh : 0 ≤ literalGapReal γ q := hcut.2.1.le.trans hcut.2.2.1
  have centered : |(l:ℝ)-q/2| ≤ M * Real.sqrt ((q:ℝ)*Real.log q) := by
    have e : (l:ℝ)-q/2 = -(literalGapReal γ q)/2 := by unfold literalGapReal l; ring
    rw [e, abs_div, abs_of_pos (show (0:ℝ)<2 by norm_num), abs_neg, abs_of_nonneg lh]
    linarith only [lh, hw]
  have hErr : A*L^2/q ≤ 1/(4*L) := by
    apply (le_div_iff₀ (show (0:ℝ)<4*L by positivity)).mpr
    change A*(L^3/q) < 1/4 at he
    nlinarith only [he, show (A*L^2/q)*(4*L) = 4*(A*(L^3/q)) by ring]
  have hh := (abs_le.mp (hu l centered)).2
  change Real.log ((q.choose l:ℝ)/(2:ℝ)^q) -
    ((Real.log (2/Real.pi)-L)/2-2*((l:ℝ)-q/2)^2/q) ≤ A*L^2/q at hh
  have quad : 2*((l:ℝ)-q/2)^2/q = (literalGapReal γ q^2/q)/2 := by
    unfold l literalGapReal
    ring
  rw [quad] at hh
  have hchoose : 0 < (q.choose l:ℝ) := by exact_mod_cast Nat.choose_pos hlq
  have hpow : 0 < (2:ℝ)^q := by positivity
  have hqγ : 0 < (q:ℝ)^γ := Real.rpow_pos_of_pos hq _
  have hB : 0 < B := div_pos hpow hqγ
  have hcpos : 0 < (2:ℝ)*(q.choose l:ℝ) := by positivity
  have logEq : Real.log (2*(q.choose l:ℝ)/B) =
      Real.log ((q.choose l:ℝ)/(2:ℝ)^q) + γ*L + Real.log 2 := by
    unfold B measurementBudget
    rw [Real.log_div hcpos.ne' (div_ne_zero hpow.ne' hqγ.ne'), Real.log_mul (by norm_num) hchoose.ne',
      Real.log_div hpow.ne' hqγ.ne', Real.log_div hchoose.ne' hpow.ne', Real.log_rpow hq]
    unfold L
    ring
  let x : ℝ := 3/(4*L)
  have logUpper : Real.log (2*(q.choose l:ℝ)/B) ≤ -x := by
    rw [logEq]
    change (2*γ-1)*L + Real.log (8/Real.pi) + 2/L ≤ literalGapReal γ q^2/q at hgap
    have errorProduct : 1/(4*L) = (1/4:ℝ)/L := by ring
    have gapProduct : 2/L = 2*(1/L) := by ring
    have xEq : x = (3/4:ℝ)/L := by unfold x; ring
    rw [errorProduct] at hErr
    rw [gapProduct] at hgap
    rw [xEq]
    nlinarith only [hgap, hh, hErr, log_double_weight_constant,
      show (1/4:ℝ)/L = (1/4)*(1/L) by ring,
      show (3/4:ℝ)/L = (3/4)*(1/L) by ring]
  have expUpper : Real.exp (-x) ≤ 1/(1+x) := by
    have hx : 0 < x := by unfold x; positivity
    apply (le_div_iff₀ (show (0:ℝ)<1+x by positivity)).mpr
    calc
      _ ≤ Real.exp (-x)*Real.exp x :=
        mul_le_mul_of_nonneg_left (by simpa [add_comm] using Real.add_one_le_exp x)
          (Real.exp_nonneg _)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have small : 1/(1+x) ≤ 1-1/(2*L) := by
    have hx : 0 < x := by unfold x; positivity
    apply (div_le_iff₀ (show (0:ℝ)<1+x by positivity)).mpr
    have e : (1-1/(2*L))*(1+x)-1 = (2*L-3)/(8*L^2) := by
      unfold x
      field_simp [hL.ne']
      ring
    apply sub_nonneg.mp
    rw [e]
    exact div_nonneg (by linarith only [hL2]) (by positivity)
  have hratio : 2*(q.choose l:ℝ)/B ≤ Real.exp (-x) := by
    rw [← Real.exp_log (div_pos hcpos hB)]
    exact Real.exp_le_exp.mpr logUpper
  have out := (div_le_iff₀ hB).mp (hratio.trans (expUpper.trans small))
  exact out.trans_eq (mul_comm _ _)

theorem literal_period_exponential_bound {q l : ℕ} (hl : 2*l < q) :
    (literalRatio q l)^(literalPeriod q l) ≤
      Real.exp (-((literalPeriod q l : ℝ)^2/((q:ℝ)+1))) := by
  let h : ℝ := literalPeriod q l
  let ρ := literalRatio q l
  have h0 : 0 ≤ h := Nat.cast_nonneg _
  have hEq : h = (q:ℝ)-2*(l:ℝ) := by
    unfold h literalPeriod
    push_cast [Nat.cast_sub (show 2*l ≤ q by omega)]
    ring
  have pos : 0 < ((q:ℝ)-l+1) := by
    have hq : (l:ℝ) ≤ q := by exact_mod_cast (show l ≤ q by omega)
    linarith
  have eq : 1-ρ = (h+1)/((q:ℝ)-l+1) := by
    unfold ρ literalRatio
    rw [hEq]
    field_simp [pos.ne']
    ring
  have hqpos : 0 < (q:ℝ)+1 := by positivity
  have lo : h/((q:ℝ)+1) ≤ 1-ρ := by
    rw [eq]
    exact (div_le_div_of_nonneg_right (show h≤h+1 by linarith) hqpos.le).trans
      (div_le_div_of_nonneg_left (by positivity) pos (by linarith [Nat.cast_nonneg (α := ℝ) l]))
  have exp : ρ ≤ Real.exp (-(1-ρ)) := by
    linarith only [Real.add_one_le_exp (-(1-ρ))]
  calc
    _ ≤ (Real.exp (-(1-ρ)))^(literalPeriod q l) :=
      pow_le_pow_left₀ (literal_ratio_nonneg (by omega)) exp _
    _ = Real.exp (h* (-(1-ρ))) := (Real.exp_nat_mul _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have e : h*(h/((q:ℝ)+1)) = h^2/((q:ℝ)+1) := by ring
      have hl := mul_le_mul_of_nonneg_left lo h0
      rw [e] at hl
      change h * (-(1-ρ)) ≤ -(h^2/((q:ℝ)+1))
      nlinarith only [hl]

def literalRhoPower (γ : ℝ) (q : ℕ) : ℝ :=
  (literalRatio q (literalCut γ q))^(literalPeriod q (literalCut γ q))

/-- The printed `rho^h ≤ q^{-c/2}` for the actual chosen cutoff. -/
theorem literal_period_power_vs_dimension (γ : ℝ) (hγ : 1/2 < γ) :
    ∀ᶠ q : ℕ in atTop, literalRhoPower γ q ≤ (q:ℝ)^(-(2*γ-1)/2) := by
  let c := 2*γ-1
  have hc : 0 < c := by dsimp only [c]; linarith
  have hw := (literal_scale_log_ratio γ).eventually
    (Ioi_mem_nhds (show (3*c/4:ℝ)<c by linarith only [hc]))
  filter_upwards [hw, literal_gap_squared_lower γ hγ, literal_cut_rounding γ hγ,
    symmetric_log_atTop.eventually_gt_atTop 0, eventually_ge_atTop (2:ℕ)] with q hw hg hr hL hq
  let l := literalCut γ q
  have q2 : (2:ℝ) ≤ q := by exact_mod_cast hq
  have qp : 0 < (q:ℝ) := by linarith only [q2]
  have q1p : 0 < (q:ℝ)+1 := by positivity
  have ratio : 2/3 ≤ (q:ℝ)/((q:ℝ)+1) :=
    (le_div_iff₀ q1p).mpr (by linarith only [q2])
  have large : (3*c/4)*Real.log q ≤ literalGapReal γ q^2/q :=
    ((lt_div_iff₀ hL).mp hw).le.trans hg
  have hEq : (literalPeriod q l:ℝ) = literalGapReal γ q := by
    unfold literalPeriod literalGapReal l
    push_cast [Nat.cast_sub hr.1.le]
    ring
  have big : (c/2)*Real.log q ≤ (literalPeriod q l:ℝ)^2/((q:ℝ)+1) := by
    rw [hEq]
    calc
      _ = ((3*c/4)*Real.log q)*(2/3) := by ring
      _ ≤ (literalGapReal γ q^2/q)*((q:ℝ)/((q:ℝ)+1)) :=
        mul_le_mul large ratio (by positivity) (div_nonneg (sq_nonneg _) qp.le)
      _ = _ := by field_simp [qp.ne']
  change (literalRatio q l)^(literalPeriod q l) ≤ (q:ℝ)^(-c/2)
  apply (literal_period_exponential_bound hr.1).trans
  rw [Real.rpow_def_of_pos qp]
  apply Real.exp_le_exp.mpr
  linarith only [big]

theorem literal_geometric_tail_little_o (γ : ℝ) (hγ : 1/2 < γ) :
    Tendsto (fun q : ℕ => Real.log q * (literalRhoPower γ q/(1-literalRhoPower γ q)))
      atTop (𝓝 0) := by
  let c := (2*γ-1)/2
  have hc : 0 < c := by unfold c; linarith
  have hrare : Tendsto (fun q : ℕ => Real.log q * (q:ℝ)^(-c)) atTop (𝓝 0) := by
    have hi := (isLittleO_log_rpow_atTop hc).tendsto_div_nhds_zero.comp dimension_atTop
    apply hi.congr
    intro q
    change Real.log q/(q:ℝ)^c = _
    rw [Real.rpow_neg (Nat.cast_nonneg q), div_eq_mul_inv]
  have q1 := symmetric_log_atTop.eventually_ge_atTop 1
  have htNonneg : ∀ᶠ q : ℕ in atTop, 0 ≤ literalRhoPower γ q :=
    (literal_cut_rounding γ hγ).mono fun q h =>
      pow_nonneg (literal_ratio_nonneg (by omega)) _
  have hlogt : Tendsto (fun q : ℕ => Real.log q*literalRhoPower γ q) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun q : ℕ => Real.log q*(q:ℝ)^(-c)) ?_ ?_ hrare
    · filter_upwards [htNonneg,q1] with q h hh
      exact mul_nonneg (by linarith only [hh]) h
    · filter_upwards [literal_period_power_vs_dimension γ hγ,q1] with q h hh
      apply mul_le_mul_of_nonneg_left _ (by linarith only [hh])
      simpa only [c, neg_div] using h
  have htail : Tendsto (literalRhoPower γ) atTop (𝓝 0) := by
    apply squeeze_zero' htNonneg ?_ hlogt
    filter_upwards [htNonneg,q1] with q h hh
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hh h
  have denom : Tendsto (fun q => 1-literalRhoPower γ q) atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1:ℝ))).sub htail
  have hd := hlogt.div denom one_ne_zero
  rw [zero_div] at hd
  apply hd.congr
  intro q
  exact mul_div_assoc _ _ _

/-- The paper's actual outer deletion weight is little-o of the budget
divided by `log q`. Dividing numerator and denominator by `2^q` is neutral. -/
theorem literal_outer_cost_negligible (γ : ℝ) (hγ : 1/2 < γ) :
    Tendsto (fun q : ℕ =>
      (2*(∑ k ∈ literalPeriodicLeft q (literalCut γ q), (q.choose k:ℝ)) /
        measurementBudget q γ)*Real.log q) atTop (𝓝 0) := by
  apply squeeze_zero' ?_ ?_ (literal_geometric_tail_little_o γ hγ)
  · filter_upwards [symmetric_log_atTop.eventually_gt_atTop 0] with q h
    have hb : 0 ≤ measurementBudget q γ :=
      div_nonneg (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg q) γ)
    exact mul_nonneg (div_nonneg (by positivity) hb) h.le
  · filter_upwards [literal_cut_rounding γ hγ, literal_central_pair_eq12 γ hγ,
      symmetric_log_atTop.eventually_gt_atTop 0, dimension_atTop.eventually_gt_atTop 0]
      with q hr hm hL hq
    let l := literalCut γ q
    let t := literalRhoPower γ q
    let P := measurementBudget q γ
    have hp : 0 < P := div_pos (by positivity) (Real.rpow_pos_of_pos hq _)
    have hlq : literalCut γ q ≤ q := by have hh := hr.1; omega
    have ht : 0 ≤ t/(1-t) := by
      have t0 : 0 ≤ t := pow_nonneg (literal_ratio_nonneg hlq) _
      have t1 : t < 1 := pow_lt_one₀ (literal_ratio_nonneg hlq)
        (literal_ratio_lt_one hr.1) (Nat.ne_of_gt (literal_period_positive hr.1))
      exact div_nonneg t0 (sub_nonneg.mpr t1.le)
    have main : 2*(q.choose l:ℝ) ≤ P := hm.trans
      (mul_le_of_le_one_right hp.le (by have := one_div_nonneg.mpr (show 0≤2*Real.log q by positivity); linarith))
    have left := literal_left_tail_cost hr.1
    change (∑ k ∈ literalPeriodicLeft q l,(q.choose k:ℝ)) ≤ (q.choose l:ℝ)*(t/(1-t)) at left
    have hb : 2*(∑ k ∈ literalPeriodicLeft q l,(q.choose k:ℝ)) ≤ P*(t/(1-t)) := by
      have w := mul_le_mul_of_nonneg_right main ht
      nlinarith only [left,w]
    have hh : 2*(∑ k ∈ literalPeriodicLeft q l,(q.choose k:ℝ))/P ≤ t/(1-t) := by
      apply (div_le_iff₀ hp).mpr
      simpa only [mul_comm P (t/(1-t))] using hb
    exact (mul_le_mul_of_nonneg_right hh hL.le).trans_eq (mul_comm _ _)

/-- The full original formula (11) with its original cutoff is affordable
and achieves the exact printed retained interval bound. -/
theorem literal_periodic_layers_fit_printed_budget (γ : ℝ) (hγ : 1/2 < γ) :
    ∀ᶠ q : ℕ in atTop,
      let l := literalCut γ q
      (∑ k ∈ literalPeriodicLayers q l, (q.choose k:ℝ)) ≤ measurementBudget q γ ∧
        symmetricDegree q γ ≤ literalPeriod q l-2 := by
  have hg := (literal_geometric_tail_little_o γ hγ).eventually
    (Iio_mem_nhds (show (0:ℝ)<1/2 by norm_num))
  filter_upwards [hg, literal_central_pair_eq12 γ hγ, literal_cut_rounding γ hγ,
    symmetric_log_atTop.eventually_gt_atTop 0, dimension_atTop.eventually_gt_atTop 0]
    with q hg hm hr hL hq
  let l := literalCut γ q
  let t := literalRhoPower γ q
  let s : ℝ := 1/(2*Real.log q)
  let B := measurementBudget q γ
  have hB : 0 < B := div_pos (by positivity) (Real.rpow_pos_of_pos hq _)
  have hlq : literalCut γ q ≤ q := by have hh := hr.1; omega
  have ht : 0 ≤ t/(1-t) := by
    have t0 : 0 ≤ t := pow_nonneg (literal_ratio_nonneg hlq) _
    have t1 : t < 1 := pow_lt_one₀ (literal_ratio_nonneg hlq)
      (literal_ratio_lt_one hr.1) (Nat.ne_of_gt (literal_period_positive hr.1))
    exact div_nonneg t0 (sub_nonneg.mpr t1.le)
  have small : t/(1-t) ≤ s := by
    change _ ≤ 1/(2*Real.log q)
    apply (le_div_iff₀ (show 0<2*Real.log q by positivity)).mpr
    change Real.log q*(t/(1-t)) < 1/2 at hg
    nlinarith only [hg]
  have main : 2*(q.choose l:ℝ) ≤ B*(1-s) := hm
  have hn : 0 ≤ B*(1-s) := (by positivity : 0 ≤ 2*(q.choose l:ℝ)).trans main
  have hcost : (∑ k ∈ literalPeriodicLayers q l,(q.choose k:ℝ)) ≤ B := by
    calc
      _ ≤ 2*(q.choose l:ℝ) * (1+t/(1-t)) := literal_periodic_total_cost hr.1
      _ ≤ (B*(1-s))*(1+s) :=
        mul_le_mul main (by linarith only [small]) (by linarith only [ht]) hn
      _ = B - B*s^2 := by ring
      _ ≤ B := sub_le_self _ (mul_nonneg hB.le (sq_nonneg _))
  have hK : literalPeriodicLayers q l ⊆ range (q+1) := by
    intro k hk
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_literalPeriodicLayers.mp hk).1)
  refine ⟨hcost, ?_⟩
  have h := symmetricDegree_le_maxGap hK (by push_cast; exact hcost)
  rwa [literal_periodic_gap hr.1] at h

end
end LocalReconstruction.Paper1Coverage

#print axioms LocalReconstruction.Paper1Coverage.literal_central_pair_eq12
#print axioms LocalReconstruction.Paper1Coverage.literal_period_exponential_bound
#print axioms LocalReconstruction.Paper1Coverage.literal_period_power_vs_dimension
#print axioms LocalReconstruction.Paper1Coverage.literal_geometric_tail_little_o
#print axioms LocalReconstruction.Paper1Coverage.literal_outer_cost_negligible
#print axioms LocalReconstruction.Paper1Coverage.literal_periodic_layers_fit_printed_budget
