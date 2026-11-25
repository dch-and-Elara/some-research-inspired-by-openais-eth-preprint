import BooleanCube.RealBudget
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace LocalReconstruction
open Filter Real
open scoped Topology
noncomputable section

def logMain (n : ℕ) : ℝ :=
  n * Real.log n - n + Real.log n / 2 + Real.log (2 * Real.pi) / 2

/-- An explicit, two-sided version of the logarithmic Stirling remainder used in (10). -/
theorem log_factorial_error (n : ℕ) (hn : 0 < n) :
    0 ≤ Real.log n.factorial - logMain n ∧
      Real.log n.factorial - logMain n ≤ 1 / (4 * (n:ℝ)) := by
  have hm := Stirling.le_log_factorial_stirling hn.ne'
  refine ⟨sub_nonneg.mpr hm,?_⟩
  let f (m : ℕ) := Real.log (Stirling.stirlingSeq (m+1)) - (1/4:ℝ) * (1/((m:ℝ)+1))
  have mono : Monotone f := by
    apply monotone_nat_of_le_succ
    intro m
    have h := Stirling.log_stirlingSeq_diff_le_geo_sum m
    have iden :
        ((1:ℝ)/(2*((m:ℝ)+1)+1))^2/(1-((1:ℝ)/(2*((m:ℝ)+1)+1))^2) =
          (1/4:ℝ)*(1/((m:ℝ)+1))-(1/4:ℝ)*(1/((m:ℝ)+2)) := by
      have hz : (2*((m:ℝ)+1)+1)^2 ≠ 0 := by positivity
      have hpos : (2*((m:ℝ)+1)+1)^2-1 ≠ 0 := by
        have hm0 : 0 ≤ (m:ℝ) := by positivity
        nlinarith [sq_nonneg (m:ℝ)]
      rw [div_pow,one_pow,one_sub_div hz,div_div_div_cancel_right₀ hz]
      field_simp [hpos]; ring
    push_cast at h
    rw [iden] at h
    dsimp [f]
    push_cast
    rw [show (m:ℝ)+1+1 = (m:ℝ)+2 by ring]
    change _ ≤ Real.log (Stirling.stirlingSeq (m+2)) - _
    linarith
  have hlim : Tendsto f atTop (𝓝 (Real.log (Real.sqrt Real.pi))) := by
    have h₁ := (Real.continuousAt_log (Real.sqrt_pos.2 Real.pi_pos).ne').tendsto.comp
      (Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1))
    have h₂ := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1/4:ℝ)
    simpa only [mul_zero,sub_zero] using h₁.sub h₂
  obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have h := mono.ge_of_tendsto hlim m
  dsimp [f] at h
  rw [Stirling.log_stirlingSeq_formula, Real.log_mul (by norm_num) (by positivity),
    Real.log_div (by positivity) (by positivity), Real.log_exp, Real.log_sqrt Real.pi_pos.le] at h
  unfold logMain
  rw [Real.log_mul (by norm_num) Real.pi_pos.ne']
  push_cast at *
  convert_to _ ≤ (1/4:ℝ)*(1/((m:ℝ)+1)) using 1
  · field_simp
  linarith

private theorem log_choose {q k : ℕ} (hk : k ≤ q) :
    Real.log (q.choose k) = Real.log q.factorial - Real.log k.factorial -
      Real.log (q-k).factorial := by
  have e : ((q.choose k:ℕ):ℝ) * k.factorial * (q-k).factorial = q.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
  have h := congrArg Real.log e
  have h₁ : (0:ℝ) < q.choose k := by exact_mod_cast Nat.choose_pos hk
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul h₁.ne' (by positivity)] at h
  linarith

/-- A uniform finite error, valid for both parities of q and for every interior k. -/
theorem binomial_log_stirling {q k : ℕ} (hk : 0 < k) (hkq : k < q) :
    |Real.log ((q.choose k : ℝ)/(2:ℝ)^q) -
      (logMain q - logMain k - logMain (q-k) - q*Real.log 2)| ≤
      1/(4*(q:ℝ)) + 1/(4*(k:ℝ)) + 1/(4*((q-k:ℕ):ℝ)) := by
  have h₁ := log_factorial_error q (by omega)
  have h₂ := log_factorial_error k hk
  have h₃ := log_factorial_error (q-k) (by omega)
  have hpos : (0:ℝ) < q.choose k := by exact_mod_cast Nat.choose_pos hkq.le
  rw [Real.log_div hpos.ne' (by positivity),Real.log_pow, log_choose hkq.le,abs_le]
  constructor <;> linarith

def centeredEntropy (t : ℝ) : ℝ :=
  ((1+t)*Real.log (1+t) + (1-t)*Real.log (1-t))/2

private theorem cubic_log (t : ℝ) (ht : |t| ≤ 1/2) :
    |Real.log (1+t) - (t-t^2/2+t^3/3)| ≤ 2*t^4 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -t)
    (by rw [abs_neg]; linarith : |-t| < 1) 3
  norm_num [Finset.sum_range_succ,abs_neg] at h
  have e : (-t + t^2/2 - t^3/3) + Real.log (1+t) =
      Real.log (1+t) - (t-t^2/2+t^3/3) := by ring
  rw [← e]
  calc
    _ ≤ |t|^4/(1-|t|) := by convert h using 2; ring
    _ ≤ 2*t^4 := by
      rw [div_le_iff₀ (by linarith : 0 < 1-|t|),show |t|^4=t^4 by exact Even.pow_abs (by decide) t]
      nlinarith [mul_nonneg (pow_nonneg (abs_nonneg t) 4) (sub_nonneg.mpr ht),
        mul_nonneg (show 0 ≤ t^4 by positivity) (sub_nonneg.mpr ht)]

theorem centered_entropy_error (t : ℝ) (ht : |t| ≤ 1/2) :
    |centeredEntropy t - t^2/2| ≤ 3*t^4 := by
  have hp := (abs_le.mp (cubic_log t ht))
  have hm := (abs_le.mp (cubic_log (-t) (by simpa using ht)))
  have h₁ : 0 ≤ 1+t := by have := (abs_le.mp ht).1; linarith
  have h₂ : 0 ≤ 1-t := by have := (abs_le.mp ht).2; linarith
  rw [abs_le]
  unfold centeredEntropy
  simp only [← sub_eq_add_neg] at hm
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hp.1 h₁,mul_le_mul_of_nonneg_left hm.1 h₂,
      (show 0 ≤ t^4 by positivity)]
  · nlinarith [mul_le_mul_of_nonneg_left hp.2 h₁,mul_le_mul_of_nonneg_left hm.2 h₂,
      (show 0 ≤ t^4 by positivity)]

private theorem entropy_form {q k : ℕ} (hk : 0 < k) (hkq : k < q) (t : ℝ)
    (ht : (q:ℝ)*t = 2*(k:ℝ)-q) :
    logMain q - logMain k - logMain (q-k) - q * Real.log 2 =
      (Real.log (2/Real.pi) - Real.log q)/2 - q * centeredEntropy t -
        Real.log (1-t^2)/2 := by
  have hq : (0:ℝ) < q := by exact_mod_cast (hk.trans hkq)
  have hu : ((k:ℕ):ℝ) = (q:ℝ)*(1+t)/2 := by linarith
  have hv : ((q-k:ℕ):ℝ) = (q:ℝ)*(1-t)/2 := by rw [Nat.cast_sub hkq.le]; linarith
  have hp : 0 < 1+t := by
    apply pos_of_mul_pos_right (a := (q:ℝ)) _ hq.le
    nlinarith [show 0 < (k:ℝ) by exact_mod_cast hk]
  have hm : 0 < 1-t := by
    apply pos_of_mul_pos_right (a := (q:ℝ)) _ hq.le
    nlinarith [show 0 < ((q-k:ℕ):ℝ) by exact_mod_cast (Nat.sub_pos_of_lt hkq)]
  unfold logMain centeredEntropy
  rw [hu,hv, Real.log_div (mul_pos hq hp).ne' (by norm_num),
    Real.log_div (mul_pos hq hm).ne' (by norm_num), Real.log_mul hq.ne' hp.ne',
    Real.log_mul hq.ne' hm.ne', Real.log_div (by norm_num) Real.pi_pos.ne',
    Real.log_mul (by norm_num) Real.pi_pos.ne',show 1-t^2=(1+t)*(1-t) by ring,
    Real.log_mul hp.ne' hm.ne']
  ring

/-- Explicit uniform local Gaussian error for the full central half of the binomial law.
Here t = 2(k-q/2)/q; the analytic error terms are q*t^4 and t^2. -/
theorem local_binomial_error {q k : ℕ} (hk : 0 < k) (hkq : k < q) (t : ℝ)
    (ht : (q:ℝ)*t = 2*(k:ℝ)-q) (hc : |t| ≤ 1/2) :
    |Real.log ((q.choose k : ℝ)/(2:ℝ)^q) -
      ((Real.log (2/Real.pi)-Real.log q)/2 - q*t^2/2)| ≤
      1/(4*(q:ℝ)) + 1/(4*(k:ℝ)) + 1/(4*((q-k:ℕ):ℝ)) + 3*q*t^4 + t^2 := by
  have hs := binomial_log_stirling hk hkq
  rw [entropy_form hk hkq t ht] at hs
  have he := abs_le.mp (centered_entropy_error t hc)
  have hq : 0 ≤ (q:ℝ) := by positivity
  have ht2 : t^2 ≤ 1/2 := by
    have := sq_le_sq' (abs_le.mp hc).1 (abs_le.mp hc).2
    nlinarith
  have hl := Real.abs_log_sub_add_sum_range_le (x := t^2)
    (by rw [abs_of_nonneg (sq_nonneg _)]; linarith) 0
  simp only [Finset.range_zero,Finset.sum_empty,zero_add,pow_one,abs_of_nonneg (sq_nonneg t)] at hl
  have hz : |Real.log (1-t^2)| ≤ 2*t^2 := hl.trans (by
    apply (div_le_iff₀ (by linarith : 0 < 1-t^2)).mpr
    nlinarith [mul_nonneg (sq_nonneg t) (show 0 ≤ 1/2 - t^2 by linarith)])
  obtain ⟨lo,hi⟩ := abs_le.mp hs
  obtain ⟨zlo,zhi⟩ := abs_le.mp hz
  apply abs_le.mpr
  constructor <;> nlinarith [mul_le_mul_of_nonneg_left he.1 hq,mul_le_mul_of_nonneg_left he.2 hq]

/-- Equation (10), with an explicit constant in the O-term depending only on M.
The event in q precedes the universal quantifier over the integer k. -/
theorem uniform_local_binomial (M : ℝ) (hM : 0 < M) :
    ∀ᶠ q : ℕ in atTop, ∀ k : ℕ,
      |(k:ℝ) - q/2| ≤ M * Real.sqrt ((q:ℝ)*Real.log q) →
      |Real.log ((q.choose k : ℝ)/(2:ℝ)^q) -
         ((Real.log (2/Real.pi)-Real.log q)/2 - 2*((k:ℝ)-q/2)^2/q)| ≤
        (3+4*M^2+48*M^4)*(Real.log q)^2/q := by
  have logs := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually
    (gt_mem_nhds (show 0 < 1/(16*M^2) by positivity))
  have large := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  filter_upwards [logs,large,eventually_ge_atTop 1] with q hs hL hq'
  intro k hk
  let Q : ℝ := q
  let L := Real.log Q
  let x := (k:ℝ)-Q/2
  let t := 2*x/Q
  have hQ : 0 < Q := by change 0 < (q:ℝ); exact_mod_cast (show 0 < q by omega)
  change L/Q < 1/(16*M^2) at hs
  change 1 ≤ L at hL
  change |x| ≤ M*Real.sqrt (Q*L) at hk
  have small := (div_lt_div_iff₀ hQ (show 0 < 16*M^2 by positivity)).mp hs
  have hx : x^2 ≤ M^2*(Q*L) := by
    have z := sq_le_sq.mpr (show |x| ≤ |M*Real.sqrt (Q*L)| by
      rwa [abs_of_nonneg (mul_nonneg hM.le (Real.sqrt_nonneg _))])
    rwa [mul_pow,Real.sq_sqrt (by positivity)] at z
  have ht : Q*t = 2*(k:ℝ)-Q := by dsimp [t,x]; field_simp
  have ht' : Q*t = 2*x := by dsimp [t]; field_simp
  have ht2 : Q*t^2 ≤ 4*M^2*L := by
    apply le_of_mul_le_mul_left (a := Q) _ hQ
    nlinarith only [hx,congrArg (fun v : ℝ => v^2) ht']
  have hc : |t| ≤ 1/2 := by
    have z : t^2 ≤ (1/2:ℝ)^2 := by
      apply le_of_mul_le_mul_left (a := Q) _ hQ
      linarith
    simpa using sq_le_sq.mp z
  have hk2 : 0 < k ∧ k < q := by
    have z := mul_le_mul_of_nonneg_left (abs_le.mp hc).1 hQ.le
    have v := mul_le_mul_of_nonneg_left (abs_le.mp hc).2 hQ.le
    have p : 0 < (k:ℝ) := by linarith
    have b : (k:ℝ) < Q := by linarith
    change (k:ℝ) < (q:ℝ) at b
    exact ⟨by exact_mod_cast p,by exact_mod_cast b⟩
  have hbase := local_binomial_error hk2.1 hk2.2 t ht hc
  have hkb : Q ≤ 4*(k:ℝ) := by
    linarith [mul_le_mul_of_nonneg_left (abs_le.mp hc).1 hQ.le]
  have hqb : Q ≤ 4*((q-k:ℕ):ℝ) := by
    rw [Nat.cast_sub hk2.2.le]
    change Q ≤ 4*(Q-k)
    linarith [mul_le_mul_of_nonneg_left (abs_le.mp hc).2 hQ.le]
  have i₁ := one_div_le_one_div_of_le hQ (show Q ≤ 4*Q by linarith)
  have i₂ := one_div_le_one_div_of_le hQ hkb
  have i₃ := one_div_le_one_div_of_le hQ hqb
  have term : Q*t^2/2 = 2*x^2/Q := by dsimp [t]; field_simp
  change |Real.log ((q.choose k:ℝ)/2^q) - ((Real.log (2/Real.pi)-L)/2 - 2*x^2/Q)| ≤ _
  rw [← term]
  refine hbase.trans ?_
  change 1/(4*Q) + 1/(4*(k:ℝ)) + 1/(4*((q-k:ℕ):ℝ)) + 3*Q*t^4 + t^2 ≤
    (3+4*M^2+48*M^4)*L^2/Q
  apply (le_div_iff₀ hQ).mpr
  have hp : 1 ≤ L^2 := by nlinarith [sq_nonneg (L-1)]
  have hlin : 4*M^2*L ≤ 4*M^2*L^2 := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith [sq_nonneg (L-1)]
  have hsq : (Q*t^2)^2 ≤ (4*M^2*L)^2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr ht2
  have hb := mul_le_mul_of_nonneg_right (add_le_add (add_le_add i₁ i₂) i₃) hQ.le
  have hi : (1/Q + 1/Q + 1/Q)*Q = 3 := by field_simp; ring
  rw [hi] at hb
  nlinarith only [hb,hp,hlin,ht2,hsq]

end
end LocalReconstruction
