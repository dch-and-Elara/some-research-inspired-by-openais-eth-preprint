import P5NativeEntryFixing
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Exact source main-entry and branch tunings. Integer ceilings are kept
visible. The largest-group argument does not need a successful design
on every branch: the source can fall back on the original n variables. -/
namespace Paper5.NativeEntry
open Real

def sourceLambda (n : ℕ) : ℕ := Nat.clog 2 n
def sourceNu (n : ℕ) : ℕ := Nat.clog 2 (sourceLambda n)
def printedGroups (n : ℕ) : ℕ := (sourceLambda n).sqrt/(sourceNu n)^2
def printedNodes (n : ℕ) : ℕ := sourceLambda n/(128*sourceNu n)
def printedWidth (n β : ℕ) : ℕ := (β+3)*ceilSqrt (sourceLambda n)

noncomputable def roundedScale (n : ℕ) : ℝ :=
  (n:ℝ)*(sourceNu n:ℝ)^2/Real.sqrt (sourceLambda n:ℝ)

theorem sourceLambda_le {d n : ℕ} (hd : d≤n) :
    sourceLambda d≤sourceLambda n := Nat.clog_mono_right 2 hd

theorem lambda_doubling {d n : ℕ} (hd : n≤2*d) :
    sourceLambda n≤sourceLambda d+1 := by
  apply (Nat.clog_le_iff_le_pow (by decide)).mpr
  rw [pow_succ']
  exact hd.trans (Nat.mul_le_mul_left _ (Nat.le_pow_clog (by decide) _))

theorem lambda_pos {d : ℕ} (hd : 2≤d) : 0<sourceLambda d :=
  (Nat.lt_clog_iff_pow_lt (by decide)).2 (by simpa using hd)

theorem nu_pos {d : ℕ} (hd : 3≤d) : 0<sourceNu d := by
  apply (Nat.lt_clog_iff_pow_lt (by decide)).2
  have h : 1<sourceLambda d := (Nat.lt_clog_iff_pow_lt (by decide)).2 (by simpa using hd)
  simpa using h

theorem nu_doubling {d n : ℕ} (hD : 3≤d) (hd : n≤2*d) :
    sourceNu n≤2*sourceNu d := by
  have hb := lambda_doubling hd
  have hL := lambda_pos (d:=d) (by omega)
  have h := (lambda_doubling (d:=sourceLambda d) (n:=sourceLambda n) (by omega))
  have h' := nu_pos hD
  change sourceNu n≤sourceNu d+1 at h
  omega

theorem sqrt_sourceLambda_pos {d : ℕ} (hd : 2≤d) :
    0<Real.sqrt (sourceLambda d:ℝ) := by
  have h := lambda_pos hd
  exact Real.sqrt_pos.mpr (by exact_mod_cast h)

theorem rounded_half_comparison {d n : ℕ} (hD : 3≤d) (hd : d≤n) (hn : n≤2*d) :
    roundedScale n≤8*roundedScale d := by
  have h := Nat.mul_le_mul hn (Nat.pow_le_pow_left (nu_doubling hD hn) 2)
  have hh : (n:ℝ)*(sourceNu n:ℝ)^2≤8*(d:ℝ)*(sourceNu d:ℝ)^2 := by
    exact_mod_cast (show n*(sourceNu n)^2≤8*d*(sourceNu d)^2 from by
      calc
        _ ≤ 2*d*(2*sourceNu d)^2 := h
        _ = _ := by ring)
  have hSq : sqrt (sourceLambda d:ℝ)≤sqrt (sourceLambda n:ℝ) :=
    sqrt_le_sqrt (by exact_mod_cast sourceLambda_le hd)
  have hdSq := sqrt_sourceLambda_pos (d:=d) (by omega)
  have hnSq := sqrt_sourceLambda_pos (d:=n) (by omega)
  unfold roundedScale
  calc
    _ ≤ (8*(d:ℝ)*(sourceNu d:ℝ)^2)/sqrt (sourceLambda n:ℝ) :=
      div_le_div_of_nonneg_right hh hnSq.le
    _ ≤ (8*(d:ℝ)*(sourceNu d:ℝ)^2)/sqrt (sourceLambda d:ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hdSq hSq
    _ = _ := by ring

theorem printed_r_times_nu_le {n : ℕ} :
    (printedGroups n:ℝ)*(sourceNu n:ℝ)^2≤sqrt (sourceLambda n:ℝ) := by
  have h₁ : printedGroups n*(sourceNu n)^2≤(sourceLambda n).sqrt :=
    Nat.div_mul_le_self _ _
  have h₂ : ((sourceLambda n).sqrt:ℝ)≤sqrt (sourceLambda n:ℝ) := by
    apply (sq_le_sq₀ (by positivity : 0≤((sourceLambda n).sqrt:ℝ)) (sqrt_nonneg _)).mp
    rw [sq_sqrt (by positivity)]
    exact_mod_cast Nat.sqrt_le' (sourceLambda n)
  exact (by exact_mod_cast h₁ : (printedGroups n:ℝ)*(sourceNu n:ℝ)^2≤_).trans h₂

theorem roundedScale_le_group_cost {n : ℕ} (hn : 2≤n) (hr : 0<printedGroups n) :
    roundedScale n ≤ (n:ℝ)/(printedGroups n:ℝ) := by
  have hg : 0<(printedGroups n:ℝ) := by exact_mod_cast hr
  unfold roundedScale
  apply (div_le_div_iff₀ (sqrt_sourceLambda_pos hn) hg).mpr
  calc
    _ = (n:ℝ)*((printedGroups n:ℝ)*(sourceNu n:ℝ)^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left printed_r_times_nu_le (by positivity)

theorem unclipped_scale_le {n : ℕ} (hn : 2≤n) (hr : 0<printedGroups n) :
    roundedScale n≤(n:ℝ) := by
  refine (roundedScale_le_group_cost hn hr).trans ?_
  have h1 : (1:ℝ)≤(printedGroups n:ℝ) := by exact_mod_cast hr
  exact div_le_self (by positivity) h1

theorem source_lambda_literal (n : ℕ) :
    sourceLambda n=⌈logb 2 (n:ℝ)⌉₊ := (Real.natCeil_logb_natCast 2 n).symm

theorem source_nu_literal (n : ℕ) :
    sourceNu n=⌈logb 2 (sourceLambda n:ℝ)⌉₊ := (Real.natCeil_logb_natCast 2 _).symm

noncomputable def binaryScale (n : ℕ) : ℝ :=
  (n:ℝ)*(logb 2 (logb 2 (n:ℝ)))^2/sqrt (logb 2 (n:ℝ))

theorem binary_le_two_rounded {n : ℕ} (hn : 2≤n) :
    binaryScale n≤2*roundedScale n := by
  let x := logb 2 (n:ℝ)
  have hx : 1≤x := by
    have he := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
      (by norm_num : (0:ℝ)<2) (show (2:ℝ)≤n by exact_mod_cast hn)
    simpa [x] using he
  have hLamge : x≤(sourceLambda n:ℝ) := by rw [source_lambda_literal]; exact Nat.le_ceil _
  have hLamle : (sourceLambda n:ℝ)≤x+1 := by
    rw [source_lambda_literal]
    exact (Nat.ceil_lt_add_one (by linarith only [hx])).le
  have hNu : logb 2 x≤(sourceNu n:ℝ) := by
    rw [source_nu_literal]
    exact (Real.logb_le_logb_of_le (by norm_num) (by linarith only [hx]) hLamge).trans
      (Nat.le_ceil _)
  have hNu₀ : 0≤logb 2 x := Real.logb_nonneg (by norm_num) hx
  have hsqrt : sqrt (sourceLambda n:ℝ) ≤ 2*sqrt x := by
    apply (sq_le_sq₀ (sqrt_nonneg _) (by positivity)).mp
    rw [sq_sqrt (by positivity),mul_pow,sq_sqrt (by linarith only [hx])]
    linarith only [hLamle,hx]
  have hc : (n:ℝ)*(logb 2 x)^2 ≤ (n:ℝ)*(sourceNu n:ℝ)^2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hNu₀ hNu 2) (by positivity)
  change (n:ℝ)*(logb 2 x)^2/sqrt x ≤ 2*((n:ℝ)*(sourceNu n:ℝ)^2/sqrt (sourceLambda n:ℝ))
  calc
    _ ≤ (n:ℝ)*(sourceNu n:ℝ)^2/sqrt x :=
      div_le_div_of_nonneg_right hc (sqrt_nonneg x)
    _ = 2*((n:ℝ)*(sourceNu n:ℝ)^2/(2*sqrt x)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (by positivity) (sqrt_sourceLambda_pos hn) hsqrt) (by norm_num)

#print axioms lambda_doubling
#print axioms nu_doubling
#print axioms rounded_half_comparison
#print axioms printed_r_times_nu_le
#print axioms roundedScale_le_group_cost
#print axioms unclipped_scale_le
#print axioms source_lambda_literal
#print axioms source_nu_literal
#print axioms binary_le_two_rounded
end Paper5.NativeEntry