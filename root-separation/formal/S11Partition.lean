
import S11Upper
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Sqrt

namespace S11

open scoped BigOperators

noncomputable def partitionConstant : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1)^2

private theorem summable_inverse_sq : Summable fun n : ℕ => 1 / ((n : ℝ) + 1)^2 := by
  have ht : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2)) 1 := by
    have hn (n : ℕ) : 0 ≤ 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 2) := by
      apply sub_nonneg.2
      exact one_div_le_one_div_of_le (by positivity) (by linarith)
    apply (hasSum_iff_tendsto_nat_of_nonneg hn _).2
    have he (n : ℕ) : (∑ i ∈ Finset.range n, (1 / ((i : ℝ) + 1) - 1 / ((i : ℝ) + 2))) =
        1 - 1 / ((n : ℝ) + 1) := by
      induction n with
      | zero => norm_num
      | succ n ih =>
        rw [Finset.sum_range_succ, ih, Nat.cast_succ]
        rw [show (n : ℝ) + 1 + 1 = n + 2 by ring]
        ring
    simp_rw [he]
    simpa using (tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat)
  refine (ht.summable.mul_left 2).of_nonneg_of_le (fun n => by positivity) ?_
  intro n
  have h1 : 0 < (n : ℝ) + 1 := by positivity
  have h2 : 0 < (n : ℝ) + 2 := by positivity
  field_simp
  nlinarith

private theorem sum_shifted_geometric {θ : ℝ} (hθ : 0 < θ) (n k : ℕ) :
    (∑ b ∈ Finset.range k, Real.exp (-θ * ((b : ℝ) + 1))^(n+1) / ((n : ℝ) + 1))
      ≤ (1 / θ) * (1 / ((n : ℝ) + 1)^2) := by
  let x := θ * ((n : ℝ) + 1)
  have hx : 0 < x := by dsimp [x]; positivity
  let q := Real.exp (-x)
  have hq : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := Real.exp_lt_one_iff.2 (neg_neg_of_pos hx)
  have hr : ∀ b : ℕ, Real.exp (-θ * ((b : ℝ) + 1))^(n+1) = q^(b+1) := by
    intro b
    change _ = Real.exp (-x)^(b+1)
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    push_cast
    unfold x
    congr 1
    ring
  simp_rw [hr, pow_succ, mul_comm _ q, mul_div_assoc, ← Finset.mul_sum, ← Finset.sum_div]
  have hsum : (∑ b ∈ Finset.range k, q^b) ≤ (1-q)⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ (sub_pos.2 hq1)).2
    rw [geom_sum_mul_neg]
    have hp : 0 ≤ q^k := pow_nonneg hq.le _
    linarith
  have hinv : q * (1 - q)⁻¹ ≤ x⁻¹ := by
    rw [← div_eq_mul_inv, ← one_div]
    apply (div_le_div_iff₀ (sub_pos.2 hq1) hx).2
    have h := Real.add_one_le_exp x
    have hh := mul_le_mul_of_nonneg_left h hq.le
    have hqe : q * Real.exp x = 1 := by simp [q, Real.exp_neg]
    rw [hqe, mul_add, mul_one] at hh
    linarith
  calc
    _ ≤ q * ((1-q)⁻¹ / ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsum (by positivity)) hq.le
    _ = (q * (1-q)⁻¹) / ((n : ℝ) + 1) := by ring
    _ ≤ x⁻¹ / ((n : ℝ) + 1) := div_le_div_of_nonneg_right hinv (by positivity)
    _ = _ := by unfold x; field_simp [hθ.ne']

theorem log_partition_bound {θ : ℝ} (hθ : 0 < θ) (k : ℕ) :
    (∑ b ∈ Finset.range k, -Real.log (1 - Real.exp (-θ * ((b : ℝ)+1)))) ≤
      partitionConstant / θ := by
  let f (b n : ℕ) := Real.exp (-θ * ((b : ℝ) + 1))^(n+1) / ((n : ℝ) + 1)
  have hf (b : ℕ) : HasSum (f b) (-Real.log (1 - Real.exp (-θ * ((b : ℝ)+1)))) := by
    have hpos : 0 < θ * ((b : ℝ) + 1) := by positivity
    apply Real.hasSum_pow_div_log_of_abs_lt_one
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.2 (by linarith)
  have hsum : HasSum (fun n => ∑ b ∈ Finset.range k, f b n)
      (∑ b ∈ Finset.range k, -Real.log (1 - Real.exp (-θ * ((b : ℝ)+1)))) := by
    exact hasSum_sum fun b _ => hf b
  have hcomp := summable_inverse_sq.mul_left (1/θ)
  rw [← hsum.tsum_eq]
  calc
    _ ≤ ∑' n : ℕ, (1 / θ) * (1 / ((n : ℝ) + 1)^2) :=
      hsum.summable.tsum_le_tsum (fun n => sum_shifted_geometric hθ n k) hcomp
    _ = _ := by rw [tsum_mul_left, partitionConstant]; ring

theorem mode_partition_bound (B : Type*) [Fintype B] (i p : ℕ) {θ : ℝ} (hθ : 0 < θ) :
    ((tuples (modeWeights B i p) p).length : ℝ) ≤
      Real.exp (θ * p + (Fintype.card B : ℝ) * 2^(i+1) * (partitionConstant / θ)) := by
  classical
  have hw : ∀ w ∈ modeWeights B i p, 0 < w := by
    intro w hw
    obtain ⟨m,_,rfl⟩ := List.mem_map.1 hw
    omega
  refine (tuple_generating_bound hθ _ hw _).trans ?_
  let f (b : Fin (p-1)) := -Real.log (1 - Real.exp (-θ * ((b.val : ℝ)+1)))
  have hg : generatingProduct θ (modeWeights B i p) =
      Real.exp ((Fintype.card B : ℝ) * 2^(i+1) * ∑ b, f b) := by
    unfold generatingProduct modeWeights modes
    rw [List.map_map, ← Multiset.prod_coe, ← Multiset.map_coe, Finset.coe_toList]
    change (∏ m : Mode B i p, (1 - Real.exp (-θ * (m.2.2.val + 1 : ℕ)))⁻¹) = _
    have hb (b : Fin (p-1)) :
        (1 - Real.exp (-θ * (b.val + 1 : ℕ)))⁻¹ = Real.exp (f b) := by
      push_cast
      unfold f
      rw [Real.exp_neg, Real.exp_log]
      apply sub_pos.2
      apply Real.exp_lt_one_iff.2
      have h : 0 < θ * ((b.val : ℝ) + 1) := by positivity
      linarith
    simp_rw [hb]
    rw [← Real.exp_sum]
    congr 1
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    ring
  have hlog : ∑ b, f b ≤ partitionConstant / θ := by
    unfold f
    rw [Fin.sum_univ_eq_sum_range (fun b : ℕ => -Real.log (1 - Real.exp (-θ * ((b : ℝ)+1))))]
    exact log_partition_bound hθ (p-1)
  rw [hg, ← Real.exp_add]
  apply Real.exp_le_exp.2
  exact add_le_add_left (mul_le_mul_of_nonneg_left hlog (by positivity)) _

theorem mode_exp_upper (B : Type*) [Fintype B] (i p : ℕ) (M D u C : ℝ)
    (hD : 0 < D) (hu : 0 < u)
    (hp : (p : ℝ) ≤ C * M * D / u)
    (hm : (Fintype.card B : ℝ) * 2^(i+1) ≤ 6*M/D) :
    ((tuples (modeWeights B i p) p).length : ℝ) ≤
      Real.exp ((C + 6 * partitionConstant) * M / Real.sqrt u) := by
  let q := Real.sqrt u
  let θ := q/D
  have hq : 0 < q := Real.sqrt_pos.2 hu
  have hqu : q*q = u := Real.mul_self_sqrt hu.le
  have hθ : 0 < θ := div_pos hq hD
  have hC : 0 ≤ partitionConstant := tsum_nonneg fun _ => by positivity
  have hprec : θ * (p : ℝ) ≤ C * M / q := by
    refine (mul_le_mul_of_nonneg_left hp hθ.le).trans_eq ?_
    unfold θ
    rw [← hqu]
    field_simp
  have hmodes : (Fintype.card B : ℝ) * 2^(i+1) * (partitionConstant/θ)
      ≤ 6 * partitionConstant * M / q := by
    refine (mul_le_mul_of_nonneg_right hm (div_nonneg hC hθ.le)).trans_eq ?_
    unfold θ
    field_simp
  refine (mode_partition_bound B i p hθ).trans (Real.exp_le_exp.2 ?_)
  apply (add_le_add hprec hmodes).trans_eq
  ring

/-- The geometric-depth factor in the source's bound on all call levels.
    Polynomial overhead per level is represented by c. -/
theorem depth_product_upper {c A r : ℝ} (hc : 0 ≤ c) (hA : 0 ≤ A)
    (hr : 0 ≤ r) (hr1 : r < 1) (depth : ℕ) :
    (∏ d ∈ Finset.range depth, c * Real.exp (A*r^d)) ≤
      c^depth * Real.exp (A / (1-r)) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← Real.exp_sum,
    ← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hc _)
  apply Real.exp_le_exp.2
  rw [div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ hA
  rw [← one_div]
  apply (le_div_iff₀ (sub_pos.2 hr1)).2
  rw [geom_sum_mul_neg]
  have h : 0 ≤ r^depth := pow_nonneg hr _
  linarith

#print axioms mode_exp_upper
#print axioms depth_product_upper
#print axioms log_partition_bound
#print axioms mode_partition_bound

end S11

