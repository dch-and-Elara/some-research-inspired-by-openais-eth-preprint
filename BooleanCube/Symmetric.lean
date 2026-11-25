import BooleanCube.SymmetricLayers
import BooleanCube.SymmetricAnalysis

namespace LocalReconstruction
open Filter
open scoped Topology
noncomputable section

private theorem positive_measurementBudget {q : ℕ} (hq : 0 < (q:ℝ)) (γ : ℝ) :
    0 < measurementBudget q γ :=
  div_pos (by positivity) (Real.rpow_pos_of_pos hq _)

private theorem feasible_symmetric_cut (γ t : ℝ) (hγ : 1/2 < γ) (ht : 0 < t) :
    ∃ l : ℕ → ℕ, (∀ᶠ q in atTop, 2*l q < q ∧ symmetricDegree q γ ≤ q-2*l q) ∧
      (∃ M : ℝ, 0 < M ∧ ∀ᶠ q : ℕ in atTop,
        (q:ℝ)-2*l q ≤ M*Real.sqrt ((q:ℝ)*Real.log q)) ∧
      Tendsto (fun q : ℕ => ((q:ℝ)-2*l q)/q) atTop (𝓝 0) ∧
      Tendsto (fun q : ℕ => ((q:ℝ)-2*l q)^2/q-(2*γ-1)*Real.log q) atTop
        (𝓝 (Real.log (8/Real.pi)+t)) := by
  obtain ⟨l, hcut, ⟨M, hM, hwindow⟩, hsmall, htail, hlimit⟩ :=
    symmetric_cut_threshold γ t hγ
  refine ⟨l, ?_, ⟨M, hM, hwindow⟩, hsmall, hlimit⟩
  have hLocCost := symmetric_local_log_cost γ M (t/8) hM (by positivity)
  have hmargin := hlimit.eventually (lt_mem_nhds (show Real.log (8/Real.pi)+t/2 <
    Real.log (8/Real.pi)+t by linarith))
  have htailmargin := htail.eventually (gt_mem_nhds (show 0 < Real.exp (t/8)-1 from
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity))))
  filter_upwards [hcut, hwindow, hmargin, htailmargin, hLocCost] with q hc hw hm htm hloc
  have hq : 0 < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hl : l q ≤ q := by omega
  have hg : 0 < (q:ℝ)-2*l q := sub_pos.mpr (by exact_mod_cast hc)
  let P := measurementBudget q γ
  have hP : 0 < P := positive_measurementBudget hq γ
  have hratio : 0 < (q.choose (l q):ℝ)/P :=
    div_pos (by exact_mod_cast Nat.choose_pos hl) hP
  have e := (abs_le.mp (hloc (l q) hl (by rwa [abs_of_pos hg]))).2
  change Real.log ((q.choose (l q):ℝ)/P) - _ ≤ t/8 at e
  change Real.log (8/Real.pi)+t/2 <
    ((q:ℝ)-2*l q)^2/q-(2*γ-1)*Real.log q at hm
  have hexp := Real.exp_le_exp.mpr (show Real.log ((q.choose (l q):ℝ)/P) ≤
    -(t/8)-Real.log 2 by linarith only [e,hm])
  rw [Real.exp_log hratio, Real.exp_sub, Real.exp_log (by norm_num : (0:ℝ)<2)] at hexp
  have pair : 2*((q.choose (l q):ℝ)/P) ≤ Real.exp (-(t/8)) := by linarith only [hexp]
  change (q:ℝ)/((q:ℝ)-2*l q)^2 < Real.exp (t/8)-1 at htm
  obtain ⟨K, hK, hgap, hcost⟩ := symmetric_periodic_layers hc
  refine ⟨hc, (symmetricDegree_le_maxGap hK ?_).trans hgap⟩
  push_cast
  apply hcost.trans
  apply (div_le_one hP).mp
  calc
    _ = (2*((q.choose (l q):ℝ)/P))*(1+(q:ℝ)/((q:ℝ)-2*l q)^2) := by ring
    _ ≤ Real.exp (-(t/8))*Real.exp (t/8) := mul_le_mul pair (by linarith [htm])
      (by positivity) (Real.exp_pos _).le
    _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

private theorem symmetric_log_cost_pair {Q a b C η u v : ℝ} (hQ : 0 < Q)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < u) (hv : 0 < v) (hcost : u+v ≤ 1)
    (hC : 2*(η+Real.log 2)+1 ≤ C)
    (ea : |Real.log u - (C/2-Real.log 2-a^2/(2*Q))| ≤ η)
    (eb : |Real.log v - (C/2-Real.log 2-b^2/(2*Q))| ≤ η) :
    C-2*η ≤ (a+b)^2/(4*Q) := by
  have outside (x p : ℝ) (hx : 0 ≤ x) (hp : 0 < p) (hpt : p ≤ 1)
      (e : |Real.log p - (C/2-Real.log 2-x^2/(2*Q))| ≤ η) : Real.sqrt Q ≤ x := by
    have logp : Real.log p ≤ 0 := Real.log_nonpos hp.le hpt
    have hlo : (1/2:ℝ) ≤ x^2/(2*Q) := by linarith only [hC, logp, (abs_le.mp e).1]
    have hs := (le_div_iff₀ (show 0 < 2*Q by positivity)).mp hlo
    apply (sq_le_sq₀ (Real.sqrt_nonneg Q) hx).mp
    rw [Real.sq_sqrt hQ.le]
    linarith only [hs]
  have hj := symmetric_gaussian_midpoint hQ
    (outside a u ha hu (by linarith only [hv, hcost]) ea)
    (outside b v hb hv (by linarith only [hu, hcost]) eb)
  let w := Real.exp (C/2-Real.log 2-η)
  have hw : 0 < w := Real.exp_pos _
  have expbound (x p : ℝ) (hp : 0 < p)
      (e : |Real.log p - (C/2-Real.log 2-x^2/(2*Q))| ≤ η) :
      w * Real.exp (-x^2/(2*Q)) ≤ p := by
    dsimp only [w]
    rw [← Real.exp_add, ← Real.exp_log hp, Real.exp_le_exp, neg_div]
    linarith only [(abs_le.mp e).1]
  have hmul := mul_le_mul_of_nonneg_left hj hw.le
  have hsum : w * (2*Real.exp (-(a+b)^2/(8*Q))) ≤ 1 := by
    rw [mul_add] at hmul
    exact hmul.trans ((add_le_add (expbound a u hu ea) (expbound b v hv eb)).trans hcost)
  have he : Real.exp (C/2-η-(a+b)^2/(8*Q)) ≤ 1 := by
    rw [show C/2-η-(a+b)^2/(8*Q) = (C/2-Real.log 2-η) + Real.log 2 + (-(a+b)^2/(8*Q)) by ring,
      Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0:ℝ)<2), mul_assoc]
    exact hsum
  have he' := Real.exp_le_one_iff.mp he
  rw [show (a+b)^2/(4*Q) = 2*((a+b)^2/(8*Q)) by ring]
  linarith only [he']

/-- Eventual upper bound with any fixed positive slack in the constant term. -/
theorem symmetric_degree_upper (γ ε : ℝ) (hγ : 1/2 < γ) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop,
      (symmetricDegree q γ:ℝ)^2/q-(2*γ-1)*Real.log q < Real.log (8/Real.pi)+ε := by
  obtain ⟨l, hcut, _, _, hlimit⟩ := feasible_symmetric_cut γ (ε/2) hγ (by positivity)
  have hnear := hlimit.eventually (gt_mem_nhds
    (show Real.log (8/Real.pi)+ε/2 < Real.log (8/Real.pi)+ε by linarith))
  filter_upwards [hcut, hnear] with q ⟨hc, hd⟩ hn
  have hd' : (symmetricDegree q γ:ℝ) ≤ (q:ℝ)-2*l q := by
    have h := (Nat.cast_le (α := ℝ)).mpr hd
    rw [Nat.cast_sub (by omega : 2*l q ≤ q)] at h
    push_cast at h
    exact h
  have hs := (sq_le_sq₀ (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans hd')).mpr hd'
  exact (sub_le_sub_right (div_le_div_of_nonneg_right hs (Nat.cast_nonneg _)) _).trans_lt hn

/-- Eventual lower bound with any fixed positive slack in the constant term. -/
theorem symmetric_degree_lower (γ ε : ℝ) (hγ : 1/2 < γ) (hε : 0 < ε) :
    ∀ᶠ q : ℕ in atTop,
      Real.log (8/Real.pi)-ε < (symmetricDegree q γ:ℝ)^2/q-(2*γ-1)*Real.log q := by
  obtain ⟨cut, hcut, ⟨M, hM, hwindow⟩, hsmall, _⟩ :=
    feasible_symmetric_cut γ 1 hγ (by norm_num)
  let g (q : ℕ) := (q:ℝ)-2*cut q
  let C (q : ℕ) := Real.log (8/Real.pi)+(2*γ-1)*Real.log q
  let η := ε/4
  have hC : Tendsto C atTop atTop :=
    tendsto_atTop_add_const_left _ _ (symmetric_log_atTop.const_mul_atTop (by linarith : 0 < 2*γ-1))
  have hlocal := symmetric_local_log_cost γ (2*(M+2)) η (by positivity) (by dsimp [η]; positivity)
  have hqtop : Tendsto (fun q : ℕ => (q:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have rootTop := Real.tendsto_sqrt_atTop.comp (hqtop.atTop_mul_atTop₀ symmetric_log_atTop)
  have hscale : Tendsto (fun q : ℕ => 4*(g q/q+1/(q:ℝ))) atTop (𝓝 0) := by
    simpa only [add_zero, mul_zero] using
      (hsmall.add tendsto_one_div_atTop_nhds_zero_nat).const_mul 4
  have hquarter := hsmall.eventually (gt_mem_nhds (show (0:ℝ)<1/4 by norm_num))
  have hround := hscale.eventually (gt_mem_nhds (show 0 < ε/2 by positivity))
  filter_upwards [hcut, hwindow, hquarter, hround, hC.eventually_ge_atTop (2*(η+Real.log 2)+1),
    hlocal, rootTop.eventually_ge_atTop 1, eventually_ge_atTop 20] with q ⟨hc, hdeg⟩
      hwin hquarter hround hlarge hloc hroot hq20
  let d := symmetricDegree q γ
  have hq : 0 < (q:ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hd : (d:ℝ) ≤ g q := by
    have h := (Nat.cast_le (α := ℝ)).mpr hdeg
    rw [Nat.cast_sub (by omega : 2*cut q ≤ q)] at h
    push_cast at h
    exact h
  have hq20' : (20:ℝ) ≤ q := by exact_mod_cast hq20
  have hqhalf : (q:ℝ)/2-1 ≤ (q/2:ℕ) := by
    have h : q ≤ 2*(q/2)+1 := by omega
    have hr : (q:ℝ) ≤ 2*((q/2:ℕ):ℝ)+1 := by exact_mod_cast h
    linarith only [hr]
  change g q/q < 1/4 at hquarter
  have hhalf : d+2 < q/2 := by
    have h := (div_lt_iff₀ hq).mp hquarter
    exact_mod_cast (show (d:ℝ)+2 < ((q/2:ℕ):ℝ) by linarith only [h, hd, hq20', hqhalf])
  obtain ⟨K, hK, hbudget, hg⟩ := exists_optimal_symmetric_layers q γ
  obtain ⟨l, hlK, r, hrK, hl, hr, hrq, hgap⟩ :=
    symmetric_central_pair hK (le_of_eq hg) hhalf
  let a := (q:ℝ)-2*l
  let b := 2*(r:ℝ)-q
  have hlr : l < r := hl.trans_lt hr
  have hlq : l ≤ q := hlr.le.trans hrq
  have ha : 0 ≤ a := sub_nonneg.mpr (by exact_mod_cast (show 2*l ≤ q by omega))
  have hb : 0 ≤ b := sub_nonneg.mpr (by exact_mod_cast (show q ≤ 2*r by omega))
  have sumdist : a+b = 2*((r-l:ℕ):ℝ) := by
    rw [Nat.cast_sub hlr.le]
    dsimp [a,b]
    ring
  have hdist : a+b ≤ 2*((d:ℝ)+2) := by
    rw [sumdist]
    have e : ((r-l:ℕ):ℝ) ≤ (d:ℝ)+2 := by exact_mod_cast hgap
    linarith only [e]
  change 1 ≤ Real.sqrt ((q:ℝ)*Real.log q) at hroot
  change g q ≤ M*Real.sqrt ((q:ℝ)*Real.log q) at hwin
  have hwin' : a+b ≤ 2*(M+2)*Real.sqrt ((q:ℝ)*Real.log q) := by
    linarith only [hdist, hd, hwin, hroot]
  have ea := hloc l hlq (by change |a| ≤ _; rw [abs_of_nonneg ha]; linarith only [hwin', hb])
  have eb := hloc r hrq (by
    rw [show (q:ℝ)-2*r = -b by dsimp [b]; ring, abs_neg, abs_of_nonneg hb]
    linarith only [hwin', ha])
  dsimp only [a,b,C] at *
  let P := measurementBudget q γ
  have hP : 0 < P := positive_measurementBudget hq γ
  have hu : 0 < (q.choose l:ℝ)/P := div_pos (by exact_mod_cast Nat.choose_pos hlq) hP
  have hv : 0 < (q.choose r:ℝ)/P := div_pos (by exact_mod_cast Nat.choose_pos hrq) hP
  have pair_cost : (q.choose l:ℝ)/P+(q.choose r:ℝ)/P ≤ 1 := by
    rw [← add_div]
    apply (div_le_one hP).mpr
    have hsum : q.choose l+q.choose r ≤ ∑ k ∈ K, q.choose k := by
      have hs : ({l,r} : Finset ℕ) ⊆ K := by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl
        · exact hlK
        · exact hrK
      simpa [Finset.sum_insert, hlr.ne] using Finset.sum_le_sum_of_subset_of_nonneg hs
        (fun k _ _ => Nat.zero_le (q.choose k))
    exact (by exact_mod_cast hsum : (q.choose l:ℝ)+q.choose r ≤ _).trans hbudget
  have eb' : |Real.log ((q.choose r:ℝ)/P) -
      ((Real.log (8/Real.pi)+(2*γ-1)*Real.log q)/2-Real.log 2-
        (2*(r:ℝ)-q)^2/(2*q))| ≤ η := by
    convert eb using 2
    ring
  have ea' : |Real.log ((q.choose l:ℝ)/P) -
      ((Real.log (8/Real.pi)+(2*γ-1)*Real.log q)/2-Real.log 2-
        ((q:ℝ)-2*l)^2/(2*q))| ≤ η := by
    convert ea using 2
    ring
  have lo := symmetric_log_cost_pair hq ha hb hu hv pair_cost hlarge ea' eb'
  have hs := (sq_le_sq₀ (add_nonneg ha hb) (by positivity : 0 ≤ 2*((d:ℝ)+2))).mpr hdist
  have divsq := div_le_div_of_nonneg_right hs (by positivity : 0 ≤ 4*(q:ℝ))
  have mid : Real.log (8/Real.pi)+(2*γ-1)*Real.log q-2*η ≤ ((d:ℝ)+2)^2/q := by
    have hm := lo.trans divsq
    rwa [show (2*((d:ℝ)+2))^2/(4*q) = ((d:ℝ)+2)^2/q by ring] at hm
  have correction : ((d:ℝ)+2)^2/q - (d:ℝ)^2/q < ε/2 := by
    change 4*(g q/q+1/(q:ℝ)) < ε/2 at hround
    calc
      _ = 4*((d:ℝ)/q+1/q) := by ring
      _ ≤ 4*(g q/q+1/q) := by gcongr
      _ < _ := hround
  change Real.log (8/Real.pi)-ε < (d:ℝ)^2/q-(2*γ-1)*Real.log q
  dsimp only [η] at mid
  linarith only [mid, correction]

/-- Theorem B for the minimum degree of the original symmetric real-budget scheme. -/
theorem symmetric_degree_asymptotic (γ : ℝ) (hγ : 1/2 < γ) :
    Tendsto (fun q : ℕ =>
      (symmetricDegree q γ:ℝ)^2/(q:ℝ) - (2*γ-1)*Real.log q)
      atTop (𝓝 (Real.log (8/Real.pi))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [symmetric_degree_upper γ ε hγ hε, symmetric_degree_lower γ ε hγ hε] with q hhi hlo
  rw [Real.dist_eq, abs_lt]
  exact ⟨by linarith only [hlo], by linarith only [hhi]⟩

end
end LocalReconstruction
