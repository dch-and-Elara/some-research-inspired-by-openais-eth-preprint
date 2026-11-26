import P5NativeEntryScaleTransfer

/-! Source branch density with the *computed* 2-CNF sparsifier
parameter, rather than a free polylogarithmic hypothesis.  The explicit
constants are coarse because only the eventual comparison is used. -/
namespace Paper5.NativeEntry

open Real Filter
open scoped Topology

def densityConstant : ℕ := 320000*1032^2*5^3

def densityThreshold : ℕ := 1+12*densityConstant

theorem computed_hash_width {n d : ℕ} (h : 2≤printedGroups n)
    (hd : 2≤d) (hhalf : n≤2*d) :
    (hashD₀ n (sparB₂ (printedGroups n) h):ℝ) ≤
      (densityConstant:ℝ)*(logb 2 (d:ℝ))^5 := by
  let x := logb 2 (d:ℝ)
  obtain ⟨h1,_,hLa⟩ := log_source_lambda_bounds hd
  change 1≤x at h1
  change (sourceLambda d:ℝ)≤x+1 at hLa
  have hL : (sourceLambda n:ℝ)≤4*x := by
    have hh : (sourceLambda n:ℝ)≤(sourceLambda d:ℝ)+1 := by
      exact_mod_cast lambda_doubling hhalf
    linarith only [hh,hLa,h1]
  have hm : (hashMu n:ℝ)≤5*x := by
    have hh : (hashMu n:ℝ)≤(sourceLambda n:ℝ)+1 := by
      unfold hashMu sourceLambda
      exact_mod_cast Nat.add_le_add_right (Nat.log_le_clog 2 n) 1
    linarith only [hh,hL,h1]
  have hB : (sparB₂ (printedGroups n) h:ℝ)≤1032*x := by
    have hh : (sparB₂ (printedGroups n) h:ℝ)≤258*(sourceLambda n:ℝ) := by
      exact_mod_cast (literal_unit_source_B_bound h).2
    linarith only [hh,hL]
  unfold hashD₀ densityConstant
  push_cast
  have hu : 0≤x := by linarith only [h1]
  calc
    _ ≤ 320000*(1032*x)^2*(5*x)^3 := by
      gcongr
    _ = _ := by ring

theorem computed_branch_density {n : ℕ} (A : Rows n) (hn : 20≤n)
    (h : 2≤printedGroups n) (hRows : A.length≤6*n)
    (hW : ∀ r∈A,(support r).card≤hashD₀ n (sparB₂ (printedGroups n) h))
    (hL : (densityThreshold:ℝ)≤logb 2 (dim A:ℝ)) :
    (branchIncidences A:ℝ)≤(dim A:ℝ)*(logb 2 (dim A:ℝ))^6 := by
  let x := logb 2 (dim A:ℝ)
  let C := (densityConstant:ℝ)
  have hdim := dim_at_least_half A hn
  have hwidth := computed_hash_width h (d:=dim A) (by omega) hdim
  have h1 : 1≤x := (by
    exact_mod_cast Nat.succ_le_of_lt (show 0<densityThreshold by unfold densityThreshold; positivity) :
      (1:ℝ)≤(densityThreshold:ℝ)).trans hL
  have hpow : 1≤x^5 := one_le_pow₀ h1
  have hC : 1+12*C≤x := by
    simpa [densityThreshold,C,x] using hL
  have hM : (branchIncidences A:ℝ)≤(dim A:ℝ)*
      (1+12*(hashD₀ n (sparB₂ (printedGroups n) h):ℝ)) := by
    exact_mod_cast (branch_incidence_bounds A hn hRows hW).2
  change _ ≤ (dim A:ℝ)*x^6
  apply hM.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ 1+12*(C*x^5) := by gcongr
    _ ≤ (1+12*C)*x^5 := by linarith only [hpow,show (1+12*C)*x^5=x^5+12*(C*x^5) by ring]
    _ ≤ x*x^5 := mul_le_mul_of_nonneg_right hC (by positivity)
    _ = x^6 := by ring

theorem eventually_branch_density :
    ∃ n₀ : ℕ, ∀ n≥n₀,∀ (A : Rows n) (h : 2≤printedGroups n),
      A.length≤6*n →
      (∀ r∈A,(support r).card≤hashD₀ n (sparB₂ (printedGroups n) h)) →
      (branchIncidences A:ℝ)≤(dim A:ℝ)*(logb 2 (dim A:ℝ))^6 := by
  have hL : Tendsto (fun d : ℕ=>logb 2 (d:ℝ)) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1:ℝ)<2)).comp tendsto_natCast_atTop_atTop
  obtain ⟨d₀,hd₀⟩ := eventually_atTop.mp
    (hL.eventually (eventually_ge_atTop (densityThreshold:ℝ)))
  refine ⟨max 20 (2*d₀),?_⟩
  intro n hn A h hRows hW
  have h20 : 20≤n := (le_max_left _ _).trans hn
  have hh : n≤2*dim A := dim_at_least_half A h20
  have hg : 2*d₀≤n := (le_max_right _ _).trans hn
  exact computed_branch_density A h20 h hRows hW (hd₀ _ (by omega))

#print axioms computed_hash_width
#print axioms computed_branch_density
#print axioms eventually_branch_density
end Paper5.NativeEntry