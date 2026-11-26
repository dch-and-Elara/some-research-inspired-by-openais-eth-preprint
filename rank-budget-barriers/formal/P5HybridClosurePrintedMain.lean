import P5HybridClosureAsymptotic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! The actual MAIN root tuning of the retained source, lines 1365–1403
and 2747–2794.  Here N is the number of vertices *after* triangle
replacement: the source receives n=4N clones and M=12N incidences. -/
namespace Paper5.HybridClosure.Printed
open scoped Topology
open Filter

def mainLambda (N : ℕ) : ℕ := Nat.clog 2 (4*N)
def mainNu (N : ℕ) : ℕ := Nat.clog 2 (mainLambda N)
def mainR (N : ℕ) : ℕ := (mainLambda N).sqrt/(mainNu N)^2
def mainQ (N : ℕ) : ℕ := mainLambda N/(128*mainNu N)
def mainCells (N : ℕ) : ℕ := (mainR N)^(2*mainQ N)

theorem main_lambda_literal (N : ℕ) : mainLambda N=⌈Real.logb 2 (4*N:ℕ)⌉₊ := by
  simpa [mainLambda] using (Real.natCeil_logb_natCast 2 (4*N)).symm

theorem main_nu_literal (N : ℕ) : mainNu N=⌈Real.logb 2 (mainLambda N:ℕ)⌉₊ := by
  simpa [mainNu] using (Real.natCeil_logb_natCast 2 (mainLambda N)).symm

theorem sqrt_nat_le_real (n : ℕ) : (n.sqrt:ℝ)≤Real.sqrt (n:ℝ) := by
  apply (sq_le_sq₀ (by positivity : 0≤(n.sqrt:ℝ)) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity)]
  exact_mod_cast Nat.sqrt_le' n

theorem real_sqrt_lt_succ_nat (n : ℕ) : Real.sqrt (n:ℝ)<(n.sqrt:ℝ)+1 := by
  apply (sq_lt_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity)]
  exact_mod_cast Nat.lt_succ_sqrt' n

theorem main_r_literal (N : ℕ) (hν : 0<mainNu N) :
    mainR N=⌊Real.sqrt (mainLambda N:ℝ)/(mainNu N:ℝ)^2⌋₊ := by
  let lam := mainLambda N
  let b := (mainNu N)^2
  let r := mainR N
  have hb : 0<b := pow_pos hν _
  have hb' : 0<(b:ℝ) := by exact_mod_cast hb
  have h1 : r*b≤lam.sqrt := Nat.div_mul_le_self _ _
  have h2 : lam.sqrt<(r+1)*b := (Nat.div_lt_iff_lt_mul hb).mp (Nat.lt_succ_self _)
  have hbe : (b:ℝ)=(mainNu N:ℝ)^2 := by simp [b]
  rw [←hbe]
  apply Eq.symm
  change ⌊Real.sqrt (lam:ℝ)/(b:ℝ)⌋₊=r
  apply Nat.floor_eq_iff (div_nonneg (Real.sqrt_nonneg _) hb'.le) |>.2
  constructor
  · apply (le_div_iff₀ hb').2
    exact (by exact_mod_cast h1 : (r:ℝ)*(b:ℝ)≤(lam.sqrt:ℝ)).trans (sqrt_nat_le_real lam)
  · apply (div_lt_iff₀ hb').2
    exact (real_sqrt_lt_succ_nat lam).trans_le (by exact_mod_cast Nat.succ_le_of_lt h2)

theorem main_q_literal (N : ℕ) (hν : 0<mainNu N) :
    mainQ N=⌊(mainLambda N:ℝ)/(128*(mainNu N:ℝ))⌋₊ := by
  let b := 128*mainNu N
  have hb : 0<b := by dsimp [b]; positivity
  have hb' : 0<(b:ℝ) := by exact_mod_cast hb
  have hlow : mainQ N*b≤mainLambda N := Nat.div_mul_le_self _ _
  have hhigh : mainLambda N<(mainQ N+1)*b :=
    (Nat.div_lt_iff_lt_mul hb).mp (by exact Nat.lt_succ_self _)
  have hB : (b:ℝ)=128*(mainNu N:ℝ) := by dsimp [b]; push_cast; rfl
  rw [←hB]
  apply Eq.symm
  apply Nat.floor_eq_iff (div_nonneg (by positivity) hb'.le) |>.2
  exact ⟨(le_div_iff₀ hb').2 (by exact_mod_cast hlow),
    (div_lt_iff₀ hb').2 (by exact_mod_cast hhigh)⟩

theorem clog_linear_tendsto (a b : ℕ) (ha : 0<a) :
    Tendsto (fun N : ℕ=>Nat.clog 2 (a*N+b)) atTop atTop := by
  apply tendsto_atTop.2
  intro k
  filter_upwards [eventually_ge_atTop ((2:ℕ)^k)] with N hN
  have hh : (2:ℕ)^k≤a*N+b := hN.trans
    ((by simpa using Nat.mul_le_mul_right N (show 1≤a by omega) : N≤a*N).trans (Nat.le_add_right _ _))
  simpa only [Nat.clog_pow 2 k (by decide : (1:ℕ)<2)] using Nat.clog_mono_right 2 hh

private theorem fourth_step (m : ℕ) (hm : 16≤m) : (m+1)^4≤2*m^4 := by
  have h : 16*(m+1)≤17*m := by omega
  have hh := Nat.pow_le_pow_left h 4
  simp only [mul_pow] at hh
  apply Nat.le_of_mul_le_mul_left _ (by decide : 0<(16:ℕ)^4)
  calc
    _ ≤ 17^4*m^4 := hh
    _ ≤ _ := by rw [←mul_assoc]; exact Nat.mul_le_mul_right _ (by decide)

private theorem fourth_dyadic (m : ℕ) (hm : 32≤m) : 1024*m^4≤(2:ℕ)^(m-1) := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have hh := fourth_step m (by omega)
    calc
      _ ≤ 1024*(2*m^4) := Nat.mul_le_mul_left _ hh
      _ = 2*(1024*m^4) := by ring
      _ ≤ 2*(2:ℕ)^(m-1) := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [show m+1-1=(m-1)+1 by omega,pow_succ']

private theorem square_step (m : ℕ) (hm : 8≤m) : (m+1)^2≤2*m^2 := by
  have h : 8*(m+1)≤9*m := by omega
  have hh := Nat.pow_le_pow_left h 2
  simp only [mul_pow] at hh
  apply Nat.le_of_mul_le_mul_left _ (by decide : 0<(8:ℕ)^2)
  calc
    _ ≤ 9^2*m^2 := hh
    _ ≤ _ := by rw [←mul_assoc]; exact Nat.mul_le_mul_right _ (by decide)

private theorem square_dyadic (m : ℕ) (hm : 8≤m) : 2*m^2≤(2:ℕ)^(m-1) := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have hh := square_step m hm
    calc
      _ ≤ 2*(2*m^2) := Nat.mul_le_mul_left _ hh
      _ ≤ 2*(2:ℕ)^(m-1) := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [show m+1-1=(m-1)+1 by omega,pow_succ']

theorem main_Q_le_lambda (N : ℕ) : mainQ N≤mainLambda N := Nat.div_le_self _ _

theorem main_r_squared (N : ℕ) : (mainR N)^2≤mainLambda N :=
  (Nat.pow_le_pow_left (Nat.div_le_self _ _) _).trans (Nat.sqrt_le' _)

theorem main_cells_dyadic (N : ℕ) :
    (mainCells N)^2≤(2:ℕ)^(mainLambda N/64) := by
  let lam := mainLambda N
  let ν := mainNu N
  let r := mainR N
  let Q := mainQ N
  have hCap : r^2≤(2:ℕ)^ν := (main_r_squared N).trans (Nat.le_pow_clog (by decide) _)
  have hDiv := Nat.div_mul_le_self lam (128*ν)
  have hMul : ν*(2*Q)*64≤lam := by
    have hr : ν*(2*Q)*64 = Q*(128*ν) := by ring
    rw [hr]
    exact hDiv
  have hexp : ν*(2*Q)≤lam/64 := (Nat.le_div_iff_mul_le (by decide)).mpr hMul
  calc
    (mainCells N)^2 = (r^2)^(2*Q) := by unfold mainCells; rw [←pow_mul,←pow_mul]; congr 1; omega
    _ ≤ ((2:ℕ)^ν)^(2*Q) := Nat.pow_le_pow_left hCap _
    _ = (2:ℕ)^(ν*(2*Q)) := (pow_mul _ _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) hexp

theorem main_printed_feasible (N : ℕ) (hν : 32≤mainNu N) :
    32≤mainR N ∧ 0<mainQ N ∧
    12*(mainCells N)^2≤4*N ∧ 2*mainQ N*(mainR N)^2≤4*N := by
  let lam := mainLambda N
  let ν := mainNu N
  have hv : 32≤ν := hν
  have hL : (2:ℕ)^(ν-1)<lam := (Nat.lt_clog_iff_pow_lt (by decide)).mp
    (show ν-1<ν by omega)
  have h9 : 1024*ν^4≤lam := (fourth_dyadic ν hv).trans hL.le
  have hlam : 8≤lam := by
    have h := (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (show 3≤ν-1 by omega)).trans hL.le
    exact h
  have hr : 32≤mainR N := by
    apply (Nat.le_div_iff_mul_le (pow_pos (show 0<ν by omega) 2)).mpr
    apply Nat.le_sqrt'.mpr
    calc
      (32*ν^2)^2=1024*ν^4 := by ring
      _ ≤ lam := h9
  have hQ : 0<mainQ N := by
    apply (Nat.le_div_iff_mul_le (by positivity : (0:ℕ)<128*ν)).mpr
    have hh : ν≤ν^4 := by
      simpa using Nat.pow_le_pow_right (show 0<ν by omega) (show 1≤(4:ℕ) by decide)
    have hg : 128*ν≤1024*ν^4 := Nat.mul_le_mul (by decide) hh
    simpa using hg.trans h9
  have hs : (2:ℕ)^(lam-1)<4*N := (Nat.lt_clog_iff_pow_lt (by decide)).mp (show lam-1<lam by omega)
  have hh : (mainCells N)^2≤(2:ℕ)^(lam/64) := main_cells_dyadic N
  refine ⟨hr,hQ,?_,?_⟩
  · calc
      _ ≤ (2:ℕ)^4 * 2^(lam/64) := Nat.mul_le_mul (by decide) hh
      _ = (2:ℕ)^(4+lam/64) := (pow_add _ _ _).symm
      _ ≤ (2:ℕ)^(lam-1) := Nat.pow_le_pow_right (by decide) (by omega)
      _ ≤ _ := hs.le
  · calc
      _ ≤ 2*lam*lam := Nat.mul_le_mul (Nat.mul_le_mul_left _ (main_Q_le_lambda N)) (main_r_squared N)
      _ = 2*lam^2 := by ring
      _ ≤ (2:ℕ)^(lam-1) := square_dyadic lam hlam
      _ ≤ _ := hs.le

theorem main_printed_eventual :
    ∀ᶠ N : ℕ in atTop, 32≤mainR N ∧ 0<mainQ N ∧
      12*(mainCells N)^2≤4*N ∧ 2*mainQ N*(mainR N)^2≤4*N := by
  have hlam : Tendsto mainLambda atTop atTop := by simpa [mainLambda] using clog_linear_tendsto 4 0 (by decide)
  have hν : Tendsto mainNu atTop atTop := by
    have h := (clog_linear_tendsto 1 0 (by decide)).comp hlam
    simpa [mainNu,Function.comp_def] using h
  filter_upwards [hν.eventually (eventually_ge_atTop 32)] with N hN
  exact main_printed_feasible N hN

#print axioms main_lambda_literal
#print axioms main_nu_literal
#print axioms main_r_literal
#print axioms main_q_literal
#print axioms clog_linear_tendsto
#print axioms main_cells_dyadic
#print axioms main_printed_feasible
#print axioms main_printed_eventual
end Paper5.HybridClosure.Printed