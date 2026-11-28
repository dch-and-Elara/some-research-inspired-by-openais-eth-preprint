import J4R43LiteralOutsideThinning
import LocalVariance

/-! Exact total variance of the *cell vector*, not a separate
worst case n-bound charged for each cell. Each edge contributes to
one ordered cell and covariance remains local to the two closed stars. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators
open IndependentThinning LocalVariance
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5000000

variable {U C : Type*} [Fintype U] [DecidableEq U] [Fintype C] [DecidableEq C]

def markProbability (w : Outcome U) : ℚ := prob (fun _=>1) w
def colourWeight (colour : U→C) (c : C) (e : U) : ℚ := if colour e=c then 1 else 0
def markValue (B : U→Finset U) (e : U) (w : Outcome U) : ℚ := signedValue B w e
def countAt (B : U→Finset U) (colour : U→C) (c : C) (w : Outcome U) : ℚ :=
  ∑ e,colourWeight colour c e * markValue B e w
def meanAt (B : U→Finset U) (colour : U→C) (c : C) : ℚ :=
  ∑ e,colourWeight colour c e * retention B e
def markScore (B : U→Finset U) (colour : U→C) (w : Outcome U) : ℚ :=
  ∑ c, (countAt B colour c w - meanAt B colour c)^2

theorem draw_nonnegative (w : Outcome U) : 0≤markProbability w :=
  prob_nonneg _ (fun _=>by norm_num) _
theorem draw_total : ∑ w : Outcome U, markProbability w=1 := sum_prob _
theorem retention_abs (B : U→Finset U) (e : U) : |retention B e|≤1 := by
  rw [retention,abs_of_nonneg (by positivity)]
  exact pow_le_one₀ (by norm_num) (by norm_num)

theorem score_variance_unified (B : U→Finset U) (colour : U→C) (D : ℕ)
    (self : ∀ e,e∈B e) (symm : ∀ e f,f∈B e→e∈B f) (short : ∀ e,(B e).card≤D) :
    (∑ w : Outcome U,markProbability w * markScore B colour w) ≤
      4*(Fintype.card U : ℚ)*(D*D:ℕ) := by
  let dep (e : U) := (B e).biUnion B
  let cov := covariance markProbability (markValue B) (retention B)
  have off (e f : U) (hf : f∉dep e) : cov e f=0 := by
    have hd : Disjoint (B e) (B f) := by
      apply Finset.disjoint_left.mpr
      intro x he hf'
      exact hf (Finset.mem_biUnion.mpr ⟨x,he,symm f x hf'⟩)
    have go := IndependentThinning.disjoint_covariance_zero (fun _ : U=>1) B e f (self e) (self f) hd
    simpa only [cov,covariance,markProbability,markValue,mul_one] using go
  have dep_card (e : U) : (dep e).card≤D*D :=
    (Finset.card_biUnion_le_card_mul (B e) B D (fun x _=>short x)).trans
      (Nat.mul_le_mul_right _ (short e))
  have hb (e f : U) : cov e f≤4 :=
    (le_abs_self _).trans (abs_covariance_le_four markProbability (markValue B) (retention B)
      draw_nonnegative draw_total (fun e w=>abs_signedValue_le_one B w e) (retention_abs B) e f)
  have swap :
      (∑ w : Outcome U,markProbability w*markScore B colour w)=
        ∑ e : U,∑ c : C,∑ f : U,colourWeight colour c e*colourWeight colour c f*cov e f := by
    unfold markScore
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    trans (∑ c : C,∑ e : U,∑ f : U,colourWeight colour c e*colourWeight colour c f*cov e f)
    · refine Finset.sum_congr rfl fun c _=>?_
      exact weighted_square_expansion markProbability (markValue B) (retention B) (colourWeight colour c)
    · exact Finset.sum_comm
  rw [swap]
  calc
    _ ≤ ∑ _e : U,(4:ℚ)*(D*D:ℕ) := by
      refine Finset.sum_le_sum fun e _=>?_
      have one :
          (∑ c : C,∑ f : U,colourWeight colour c e*colourWeight colour c f*cov e f) =
           ∑ f : U,colourWeight colour (colour e) f*cov e f := by
        rw [Finset.sum_eq_single (colour e)]
        · simp [colourWeight]
        · intro c _ hc
          simp [colourWeight,Ne.symm hc]
        · simp
      rw [one]
      calc
        _ = ∑ f∈dep e,colourWeight colour (colour e) f*cov e f :=
          (Finset.sum_subset (Finset.subset_univ _) (fun f _ notMem=>by rw [off e f notMem,mul_zero])).symm
        _ ≤ ∑ _f∈dep e,(4:ℚ) := by
          refine Finset.sum_le_sum fun f _=>?_
          by_cases H : colour f=colour e
          · simpa [colourWeight,H] using hb e f
          · simp [colourWeight,H]
        _ ≤ (4:ℚ)*(D*D:ℕ) := by
          rw [Finset.sum_const,nsmul_eq_mul]
          norm_cast
          exact (Nat.mul_le_mul_right 4 (dep_card e)).trans_eq (Nat.mul_comm _ _)
    _ = _ := by simp [nsmul_eq_mul]; ring

theorem low_score_positive_mass (μ s : Outcome U→ℚ) (H : ℚ)
    (nonneg : ∀ w,0≤μ w) (mass : ∑ w, μ w=1)
    (avg : (∑ w,μ w*s w)≤H) :
    ∃ w,0<μ w ∧ s w≤H := by
  by_contra! bad
  obtain ⟨w,hw⟩ : ∃ w,0<μ w := by
    by_contra! none
    have z : (∑ w,μ w)=0 := Finset.sum_eq_zero (fun w _=>le_antisymm (none w) (nonneg w))
    rw [mass] at z
    norm_num at z
  have hi : (∑ w,μ w*H)< ∑ w,μ w*s w := by
    apply Finset.sum_lt_sum
    · intro q _
      by_cases fit : 0<μ q
      · exact mul_le_mul_of_nonneg_left (bad q fit).le (nonneg q)
      · simp [le_antisymm (not_lt.mp fit) (nonneg q)]
    · exact ⟨w,Finset.mem_univ _,mul_lt_mul_of_pos_left (bad w hw) hw⟩
  rw [←Finset.sum_mul,mass,one_mul] at hi
  linarith

theorem real_count_for_supported_marks (B : U→Finset U) (w : Outcome U)
    (hw : 0<markProbability w) (e : U) :
    markValue B e w = if ∀ f∈B e,(w f).1=decide (f=e) then 1 else 0 := by
  have pos : (w e).2=true := by
    by_contra hn
    have H : coinWeight (1:ℚ) (w e)=0 := by simp [coinWeight,hn]
    have Z : markProbability w=0 := Finset.prod_eq_zero (Finset.mem_univ e) H
    exact (lt_irrefl _ (Z ▸ hw))
  unfold markValue signedValue
  simp [pos,BangCore.bitSign]

theorem all_cells_close (B : U→Finset U) (colour : U→C) (D : ℕ)
    (self : ∀ e,e∈B e) (symm : ∀ e f,f∈B e→e∈B f) (short : ∀ e,(B e).card≤D)
    (margin : ℚ) (hp : 0≤margin) (hsize : 4*(Fintype.card U : ℚ)*(D*D:ℕ)≤margin^2) :
    ∃ w : Outcome U, 0<markProbability w ∧
      ∀ c, |countAt B colour c w - meanAt B colour c|≤margin := by
  obtain ⟨w,pm,good⟩ := low_score_positive_mass markProbability (markScore B colour)
    _ draw_nonnegative draw_total (score_variance_unified B colour D self symm short)
  refine ⟨w,pm,fun c=>?_⟩
  have single : (countAt B colour c w-meanAt B colour c)^2≤markScore B colour w :=
    Finset.single_le_sum (fun c' _=>sq_nonneg (countAt B colour c' w-meanAt B colour c')) (Finset.mem_univ c)
  have total := (single.trans good).trans hsize
  rw [←sq_abs (countAt B colour c w-meanAt B colour c)] at total
  exact (sq_le_sq₀ (abs_nonneg _) hp).mp total

#print axioms draw_nonnegative
#print axioms draw_total
#print axioms retention_abs
#print axioms score_variance_unified
#print axioms low_score_positive_mass
#print axioms real_count_for_supported_marks
#print axioms all_cells_close
end
end J4R43LiteralOutside

