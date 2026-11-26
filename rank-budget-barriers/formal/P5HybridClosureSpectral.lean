import P5HybridClosurePrintedD
import Mathlib.Data.Real.Sqrt

/-! Optional spectral interface. This imports neither a Ramanujan
existence axiom nor a graph-family constructor. Given the cubic
Poincare (mean-zero energy) bound with the MSS spectral constant, it
certifies the elementary real-to-rational cut inference. -/
namespace Paper5.HybridClosure.Printed
open scoped BigOperators
open GraphCutMoments

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

omit [Nonempty V] in
private theorem cutBit_sum (S : Finset V) : (∑ v,(cutBit ℝ S v))=(S.card:ℝ) := by
  unfold cutBit
  rw [←Finset.natCast_card_filter]
  simp

private theorem mean_zero_cut (S : Finset V) :
    ∑ v,(cutBit ℝ S v-(S.card:ℝ)/Fintype.card V)=0 := by
  have hN : 0<(Fintype.card V:ℝ) := by exact_mod_cast (Fintype.card_pos (α:=V))
  rw [Finset.sum_sub_distrib,cutBit_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  field_simp [hN.ne']
  simp

private theorem centered_cut_energy (S : Finset V) :
    ∑ v,(cutBit ℝ S v-(S.card:ℝ)/Fintype.card V)^2 =
      (S.card:ℝ)*(1-(S.card:ℝ)/Fintype.card V) := by
  let x : ℝ := S.card
  let n : ℝ := Fintype.card V
  let c := x/n
  have hn : 0<n := by dsimp [n]; exact_mod_cast (Fintype.card_pos (α:=V))
  change (∑ v,(cutBit ℝ S v-c)^2)=x*(1-x/n)
  have hsum : (∑ v,cutBit ℝ S v)=x := cutBit_sum S
  calc
    _ = ∑ v,(cutBit ℝ S v+ (c^2-2*c*cutBit ℝ S v)) := by
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : v∈S
      · simp [cutBit,hv]; ring
      · simp [cutBit,hv]
    _ = x+(n*c^2-2*c*x) := by
      rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
        ←Finset.mul_sum,hsum]
    _ = _ := by unfold c; field_simp [hn.ne']; ring

theorem centered_cut_ge_half_small_side (S : Finset V) :
    ((min S.card (Fintype.card V-S.card):ℕ):ℝ)/2 ≤
      ∑ v,(cutBit ℝ S v-(S.card:ℝ)/Fintype.card V)^2 := by
  rw [centered_cut_energy]
  let x : ℝ := S.card
  let n : ℝ := Fintype.card V
  have hn : 0<n := by dsimp [n]; exact_mod_cast (Fintype.card_pos (α:=V))
  have hnon : 0≤x := by dsimp [x]; positivity
  have hSN : S.card≤Fintype.card V := Finset.card_le_univ S
  have hx : x≤n := by dsimp [x,n]; exact_mod_cast hSN
  by_cases h : S.card≤Fintype.card V-S.card
  · rw [min_eq_left h]
    have h' : x≤n-x := by
      have h'' : 2*x≤n := by
        dsimp [x,n]
        exact_mod_cast (show 2*S.card≤Fintype.card V by omega)
      linarith only [h'']
    have hdiv : x/n≤1/2 := (div_le_iff₀ hn).mpr (by linarith only [h'])
    exact (show x/2=x*(1/2) by ring).le.trans
      (mul_le_mul_of_nonneg_left (by linarith only [hdiv]) hnon)
  · rw [min_eq_right (Nat.le_of_not_ge h),Nat.cast_sub hSN]
    have h' : n-x≤x := by
      have hc : n≤2*x := by dsimp [n,x]; exact_mod_cast (show Fintype.card V≤2*S.card by omega)
      linarith only [hc]
    have hdiv : 1/2≤x/n := (le_div_iff₀ hn).mpr (by linarith only [h'])
    change (n-x)/2 ≤ x*(1-x/n)
    have he : x*(1-x/n)=(n-x)*(x/n) := by field_simp [hn.ne']
    rw [he]
    calc
      _ = (n-x)*(1/2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdiv (sub_nonneg.mpr hx)

theorem ramanujan_gap_gt_sixth : (1/6:ℝ)<3-2*Real.sqrt 2 := by
  have h : Real.sqrt 2 < 17/12 := by
    apply (sq_lt_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity)]
    norm_num
  linarith

/-- An already supplied spectral Poincare certificate, not existence of a
graph or of its certificate, entails the rational constant used by E1. -/
theorem expansion_from_mss_spectral_certificate (E : Finset (V×V))
    (gap : ∀ f : V→ℝ,(∑v,f v)=0 →
      (3-2*Real.sqrt 2)*(∑v,(f v)^2)≤∑ e∈E,(f e.1-f e.2)^2) :
    ∀ S : Finset V,(1/12:ℚ)*(min S.card (Fintype.card V-S.card):ℕ)≤
      ((boundary E S).card:ℚ) := by
  intro S
  let f := fun v : V=>cutBit ℝ S v-(S.card:ℝ)/Fintype.card V
  have hf : (∑v,f v)=0 := mean_zero_cut S
  have hh := gap f hf
  have hval (e : V×V) : f e.1-f e.2=cutDifference ℝ S e := by unfold f cutDifference; ring
  simp_rw [hval,cut_energy_eq_boundary] at hh
  have hl := centered_cut_ge_half_small_side S
  have hn : 0≤(∑v,(f v)^2) := Finset.sum_nonneg (fun v _=>sq_nonneg _)
  have he := (mul_le_mul_of_nonneg_right ramanujan_gap_gt_sixth.le hn).trans hh
  have hr := (mul_le_mul_of_nonneg_left hl (by norm_num : (0:ℝ)≤1/6)).trans he
  apply (Rat.cast_le (K:=ℝ)).mp
  push_cast at hr ⊢
  linarith only [hr]

#print axioms centered_cut_ge_half_small_side
#print axioms ramanujan_gap_gt_sixth
#print axioms expansion_from_mss_spectral_certificate
end Paper5.HybridClosure.Printed