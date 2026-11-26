import P5MainBalanceM6Bias
import P5MainBalanceM6TailMarkov
import P5MainBalanceM6TailSchedule

/-! Original ordered-pair weight distribution and the exact kept-row
count. The proved constant is deliberately elementary and sufficient
for the printed M.6 scale and the source tail guard. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator Real Filter
open scoped BigOperators Classical

variable {I B : Type*} [Fintype I] [Fintype B] [LinearOrder B] [Nonempty B]

noncomputable def negIndicator (p : B×B) : ℝ := if p.2<p.1 then 1 else 0

noncomputable def axisMean (B : Type*) [Fintype B] : ℝ :=
  ((Fintype.card B:ℝ)-1)/(2*(Fintype.card B:ℝ))

omit [Nonempty B] [Fintype B] in
theorem negIndicator_bounds (x : B×B) : 0≤negIndicator x ∧ negIndicator x≤1 := by
  unfold negIndicator
  split <;> norm_num

omit [LinearOrder B] in
theorem axisMean_bounds : 0≤axisMean B ∧ axisMean B≤1 := by
  have h0 : (1:ℝ)≤Fintype.card B := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card B)
  unfold axisMean
  constructor
  · exact div_nonneg (by linarith only [h0]) (by positivity)
  · apply (div_le_iff₀ (by positivity)).mpr
    linarith only [h0]

theorem axisMean_sum : (∑ x : B×B,negIndicator x)=(Fintype.card (B×B):ℝ)*axisMean B := by
  have hh : 0<(Fintype.card (B×B):ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0<Fintype.card (B×B))
  unfold negIndicator
  rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
  change ((negativeAxis (B:=B)).card:ℝ)=_
  exact (div_eq_iff hh.ne').mp (negative_axis_probability (B:=B)) |>.trans (mul_comm _ _)

omit [Fintype B] [Nonempty B] in
theorem descending_weight_sum (u : WordCell I B) :
    (descendingWeight u:ℝ)=∑ i,negIndicator (u i) := by
  unfold descendingWeight negIndicator
  rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]

set_option maxHeartbeats 8000000 in
theorem actual_exceptional_fraction (keep : ℕ→Prop) (R : ℕ)
    (hQ : 0<Fintype.card I) (hR : R≤Fintype.card I)
    (hOut : ∀ j : ℕ,keep j →
      (R:ℝ)/4≤|(j:ℝ)-(Fintype.card I:ℝ)*axisMean B|) :
    (Fintype.card (Exceptional (Unequal (I:=I) (B:=B)) keep):ℝ)/
      (Fintype.card (WordCell I B):ℝ)
        ≤ 2*exp (-(R:ℝ)^2/(64*(Fintype.card I:ℝ))) := by
  let Q : ℝ := Fintype.card I
  let T : ℝ := (R:ℝ)/(8*Q)
  have hQ' : 0<Q := by change (0:ℝ)<(Fintype.card I:ℝ); exact_mod_cast hQ
  have hR' : (R:ℝ)≤Q := by change (R:ℝ)≤(Fintype.card I:ℝ); exact_mod_cast hR
  have ht0 : 0≤T := by dsimp only [T]; positivity
  have ht1 : T≤1 := by
    dsimp only [T]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hR',hQ']
  have h := word_two_sided_tail (I:=I) negIndicator (axisMean B) T ((R:ℝ)/4)
    negIndicator_bounds (axisMean_bounds (B:=B)).1 (axisMean_bounds (B:=B)).2 axisMean_sum ht0 ht1
  have hu : Q*T^2-T*((R:ℝ)/4)=-(R:ℝ)^2/(64*Q) := by
    dsimp only [T]
    field_simp
    ring
  change _≤2*exp (Q*T^2-T*((R:ℝ)/4)) at h
  rw [hu] at h
  have hSub : Finset.univ.filter (fun u : WordCell I B=>keep (descendingWeight u))
        ⊆ Finset.univ.filter (fun u : WordCell I B=>
          (R:ℝ)/4≤|(∑ i,negIndicator (u i))-(Fintype.card I:ℝ)*axisMean B|) := by
    intro x hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rw [←descending_weight_sum]
    exact hOut _ (Finset.mem_filter.mp hx).2
  have hc := Finset.card_le_card hSub
  rw [exceptional_count_is_weight_tail]
  exact (div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)).trans h

set_option maxHeartbeats 10000000 in
theorem printed_actual_exceptional_power (n : ℕ) (hLam : 2≤mainLambda n)
    (hr : 2≤mainAlphabet n) (hR : 32≤mainWidth 1 n) (hQR : 6*mainWidth 1 n≤mainNodes n) :
      let I := Fin (mainNodes n)
      let B := Fin (mainAlphabet n)
      (Fintype.card (Exceptional (Unequal (I:=I) (B:=B))
        (outsideInterval (printedStart n) (mainWidth 1 n))):ℝ)
        ≤ (Fintype.card (WordCell I B):ℝ)/(mainLambda n:ℝ)^5 := by
  dsimp only
  have hQ : 0<mainNodes n := by omega
  letI : Nonempty (Fin (mainAlphabet n)) := ⟨⟨0,by omega⟩⟩
  have hMean : (Fintype.card (Fin (mainNodes n)):ℝ)*axisMean (Fin (mainAlphabet n))=printedMean n := by
    unfold axisMean printedMean
    rw [Fintype.card_fin,Fintype.card_fin]
    ring
  have h := actual_exceptional_fraction (I:=Fin (mainNodes n)) (B:=Fin (mainAlphabet n))
    (outsideInterval (printedStart n) (mainWidth 1 n)) (mainWidth 1 n)
    (by rwa [Fintype.card_fin]) (by rw [Fintype.card_fin]; omega)
    (fun j hj=>by rw [hMean]; exact printed_interval_tail_deviation n j hr hR hQR hj)
  rw [Fintype.card_fin] at h
  letI : Nonempty (WordCell (Fin (mainNodes n)) (Fin (mainAlphabet n))) :=
    ⟨fun _=>(Classical.choice inferInstance,Classical.choice inferInstance)⟩
  have hD : 0<(Fintype.card (WordCell (Fin (mainNodes n)) (Fin (mainAlphabet n))):ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0<Fintype.card (WordCell _ _))
  simp only [←Nat.card_eq_fintype_card] at h hD ⊢
  have hg := (div_le_iff₀ hD).mp (h.trans (printed_R_tail_power n hLam hQ))
  exact hg.trans_eq (by ring)

theorem eventual_printed_actual_tail :
    ∀ᶠ n : ℕ in atTop,
      let I := Fin (mainNodes n)
      let B := Fin (mainAlphabet n)
      (Fintype.card (Exceptional (Unequal (I:=I) (B:=B))
        (outsideInterval (printedStart n) (mainWidth 1 n))):ℝ)
        ≤ (Fintype.card (WordCell I B):ℝ)/(mainLambda n:ℝ)^5 := by
  filter_upwards [lambda_ge_along_sizes 2,printed_balance_threshold 2,printed_width_interval_eventually] with n hL hB hR
  exact printed_actual_exceptional_power n (by exact_mod_cast hL) (by omega) hR.1 hR.2

#print axioms axisMean_sum
#print axioms descending_weight_sum
#print axioms actual_exceptional_fraction
#print axioms printed_actual_exceptional_power
#print axioms eventual_printed_actual_tail
end P5MainBalance.M6
