import P5MainIteratorPaid
import P5MainIteratorDense
import P5MainIteratorOptimize

/-! F.A4 branch assembly at a finite input size. Scalar margins
are stated numerically (not as assumptions about the cost conclusion);
a separate asymptotic layer makes them eventual. -/
namespace P5MainIterator
open scoped BigOperators Classical
open Real

theorem floor_linear_cost {V : Type*} [Fintype V] [DecidableEq V]
    (q T : ℕ) (a x : ℝ) (ha : 1≤a) (hN : a≤(Fintype.card V:ℝ))
    (hx : 2*a≤x) (hq : ⌊x⌋₊≤q) (ht : (TaylorList V q).card≤T) :
    a≤logTwo T := by
  have hs := Nat.lt_floor_add_one x
  have hi : (↑⌊x⌋₊:ℝ)≤(q:ℝ) := by exact_mod_cast hq
  have hA : a≤(q:ℝ) := by linarith only [hs,hi,hx,ha]
  have hh : a≤(↑(min q (Fintype.card V)):ℝ) := by
    rw [Nat.cast_min]
    exact le_min hA hN
  exact hh.trans (taylor_linear_cost q T ht)

variable {E V F Copy I B : Type*} [Fintype E] [Fintype V]
  [Fintype Copy] [Fintype I] [Fintype B] [LinearOrder B]

set_option maxHeartbeats 10500000 in
theorem finite_FA4 (Lyt : SourceLayout E V F Copy I B) [Nonempty E]
    (tm tg : I) (g : B) (q T R : ℕ) (L l κ δ cutoff : ℝ)
    (omitted : Finset ℕ) (hOmit : omitted.card≤R)
    (P : SourceVisits (fun j=>j∉omitted) Lyt tm tg g q T)
    (hr : 2≤Fintype.card B) (hR0 : 1≤R)
    (hQ0 : 0<Fintype.card I)
    (hcap : ∀ u,cellLoad Lyt u * Fintype.card (WordCell I B) ≤2*Fintype.card E)
    (hL : 0<L) (hl : 0<l) (hκ : 0<κ) (hδ : 0<δ) (hδκ : δ≤κ/32) (hδ1 : δ≤1)
    (_hc : 0<cutoff)
    (horder : ⌊κ*(Fintype.card V:ℝ)*(R:ℝ)/(Fintype.card I:ℝ)⌋₊≤q)
    (hlogM : log (2*(Fintype.card E:ℝ))≤2*L)
    (hA : 1≤(Fintype.card V:ℝ)*targetScale L l)
    (hα1 : targetScale L l≤1)
    (hαcut : (targetScale L l)*cutoff*l≤κ/4)
    (hακ : targetScale L l≤κ/64)
    (hαdec : targetScale L l≤exp (-l/4))
    (hscale : l/sqrt L≤exp (-l/4))
    (hsize : 2≤δ*(Fintype.card V:ℝ)*l/sqrt L)
    (hthreshold : l/4≤log tailConstant-log (2*targetScale L l))
    (hdense : cutoff*l<(Fintype.card I:ℝ) →
      256≤Fintype.card I ∧
      2*(Fintype.card E:ℝ)*(markBase*(3/4:ℝ))^Fintype.card I≤(Fintype.card V:ℝ)/2) :
    min 1 (δ/(8*log 2)) * ((Fintype.card V:ℝ)*targetScale L l) ≤ logTwo T := by
  let N := Fintype.card V
  let Q := Fintype.card I
  let r := Fintype.card B
  let α := targetScale L l
  have hn : 0<N := by
    have hn' : (N:ℝ)≠0 := by
      intro h
      have hg : 1≤(N:ℝ)*α := hA
      rw [h,zero_mul] at hg
      norm_num at hg
    exact Nat.pos_of_ne_zero (by exact_mod_cast hn')
  have hn' : 0<(N:ℝ) := by exact_mod_cast hn
  have hQr : 0<(Q:ℝ) := by exact_mod_cast hQ0
  have hr' : 0<(r:ℝ) := by exact_mod_cast (by omega : 0<r)
  have hRr : 1≤(R:ℝ) := by exact_mod_cast hR0
  have hαp : 0<α := by dsimp [α,targetScale]; positivity
  have H := actual_visits_counts (fun j=>j∉omitted) Lyt tm tg g q T P
  have hcost (h : (N:ℝ)*α≤logTwo T) : _ ≤ logTwo T :=
    ((mul_le_mul_of_nonneg_right (min_le_left (1:ℝ) (δ/(8*log 2))) (by positivity)).trans_eq
      (one_mul ((N:ℝ)*α))).trans h
  by_cases hsmall : (r:ℝ)*α≤1
  · apply hcost
    apply ((le_div_iff₀ hr').mpr ?_).trans (group_average_cost _ Lyt tm tg g q T P)
    calc
      ((N:ℝ)*α)*(r:ℝ) = ((r:ℝ)*α)*(N:ℝ) := by ring
      _ ≤ (N:ℝ) := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hsmall hn'.le
  have hlarge : 1/α<(r:ℝ) := (div_lt_iff₀ hαp).mpr (lt_of_not_ge hsmall)
  have hlogr : l/4≤log (r:ℝ) := by
    have h₁ := log_lt_log (by positivity : 0<1/α) hlarge
    have h₂ := log_le_log hαp hαdec
    rw [one_div,log_inv] at h₁
    rw [log_exp] at h₂
    linarith only [h₁,h₂]
  have hQcap : (Q:ℝ)≤4*L/l := by
    apply (le_div_iff₀ hl).mpr
    have hp := cell_feasibility_logs Lyt hr hcap
    have h := mul_le_mul_of_nonneg_left hlogr (show 0≤2*(Q:ℝ) by positivity)
    linarith only [hp,h,hlogM]
  have hAN : (N:ℝ)*α≤(N:ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hα1 hn'.le
  by_cases hsQ : (Q:ℝ)≤cutoff*l
  · apply hcost
    apply floor_linear_cost q T ((N:ℝ)*α) _ hA hAN _ horder H.1
    apply (le_div_iff₀ hQr).mpr
    calc
      _ = (2*(N:ℝ))*(α*(Q:ℝ)) := by ring
      _ ≤ (2*(N:ℝ))*(α*(cutoff*l)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsQ hαp.le) (by positivity)
      _ ≤ (2*(N:ℝ))*(κ/4) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith only [hαcut]
      _ ≤ κ*(N:ℝ)*1 := by nlinarith only [mul_pos hκ hn']
      _ ≤ _ := mul_le_mul_of_nonneg_left hRr (by positivity)
  by_cases hsR : Q<16*R
  · apply hcost
    apply floor_linear_cost q T ((N:ℝ)*α) _ hA hAN _ horder H.1
    apply (le_div_iff₀ hQr).mpr
    have hi : (Q:ℝ)≤16*(R:ℝ) := by exact_mod_cast hsR.le
    calc
      _ = (N:ℝ)*((2*α)*(Q:ℝ)) := by ring
      _ ≤ (N:ℝ)*((κ/16)*(16*(R:ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hn'.le
        apply mul_le_mul _ hi (by positivity) (by positivity)
        linarith only [hακ,hκ]
      _ = _ := by ring
  by_cases hb : (N:ℝ)*α≤logTwo T
  · exact hcost hb
  have hh := hdense (lt_of_not_ge hsQ)
  have hy := finite_FA3 Lyt tm R omitted hOmit hr hh.1 (by omega) hcap hh.2
  let Y := (Set.range (sourceTuple (fun j=>j∉omitted) Lyt tm)).ncard
  have hy0 : 0<Y := (Nat.pow_pos (by decide : 0<2)).trans_le (cube_attained (fun j=>j∉omitted) Lyt tm)
  have htY : (Y:ℝ)≤(T:ℝ) := by exact_mod_cast H.2.1
  have hlog := div_le_div_of_nonneg_right
    (log_le_log (show 0<(Y:ℝ) by exact_mod_cast hy0) htY) (log_nonneg (by norm_num : (1:ℝ)≤2))
  have hwidth := tail_forces_width_ratio N Q R (logTwo T) L l hn hQ0 hL hl hQcap
    (hy.trans hlog) (lt_of_not_ge hb) hthreshold
  have hf := entropy_selected_width q T Q R L l κ δ hL hl hκ hδ hδκ hδ1 hscale hsize hwidth horder H.1
  have hcmin := mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) (δ/(8*log 2)))
    (show 0≤(N:ℝ)*α by positivity)
  exact hcmin.trans (by simpa only [mul_assoc] using hf)

#print axioms floor_linear_cost
#print axioms finite_FA4
end P5MainIterator
