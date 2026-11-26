import P5MainIteratorBranches
import P5MainIteratorAsymptoticScalar
import P5MainIteratorAsymptoticDensity

/-! F.A4 with the originally printed base-two scale. The cutoff is
uniform in label dimensions, omitted weights, layout and evaluator. -/
namespace P5MainIterator
open scoped BigOperators Classical
open Real Filter

noncomputable def fromNaturalLogScale : ℝ := ((1+|log (log 2)|)/log 2)^2

theorem fromNaturalLogScale_pos : 0<fromNaturalLogScale := by
  unfold fromNaturalLogScale
  have h₁ : 0<log 2 := log_pos (by norm_num)
  positivity

theorem scale_compare_binary (x : ℝ) (hx : 1<x) (hl : 1≤log (log x)) :
    targetScale (logTwo x) (logTwo (logTwo x)) ≤
      fromNaturalLogScale * targetScale (log x) (log (log x)) := by
  let L := log x
  let l := log L
  let b := log 2
  have hL : 0<L := log_pos hx
  have hb : 0<b := log_pos (by norm_num)
  have hb' : b≤1 := by
    dsimp [b]
    have h := log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num)
    norm_num at h
    exact h
  have hlogb : log b≤0 := log_nonpos hb.le hb'
  have hpow : 0≤(l-log b)/b := by
    apply div_nonneg _ hb.le
    linarith only [hl,hlogb]
  have hlb : (l-log b)/b ≤ ((1+|log b|)/b)*l := by
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hb.le
    have h := mul_le_mul_of_nonneg_left hl (abs_nonneg (log b))
    nlinarith only [h,neg_abs_le (log b)]
  have hnorm : sqrt L≤sqrt (L/b) := by
    apply sqrt_le_sqrt
    apply (le_div_iff₀ hb).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hb' hL.le]
  have h₂ : 0<sqrt L := sqrt_pos.2 hL
  have hL₂ : 0<logTwo x := div_pos hL hb
  have hzip : logTwo (logTwo x)=(l-log b)/b := by
    unfold logTwo
    rw [log_div hL.ne' hb.ne']
  unfold fromNaturalLogScale targetScale
  rw [hzip]
  change ((l-log b)/b)^2 / sqrt (L/b) ≤ (((1+|log b|)/b)^2)*(l^2/sqrt L)
  calc
    _ ≤ ((l-log b)/b)^2 / sqrt L :=
      div_le_div_of_nonneg_left (sq_nonneg _) h₂ hnorm
    _ ≤ ((((1+|log b|)/b)*l)^2) / sqrt L :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hpow hlb 2) h₂.le
    _ = _ := by ring

universe u
set_option maxHeartbeats 14000000 in
theorem eventual_FA4 (β κ : ℝ) (hβ : 0≤β) (hκ : 0<κ) :
    ∃ c : ℝ, 0<c ∧ ∃ n₀ : ℕ,
      ∀ {E V F Copy I B : Type u} [Fintype E] [Fintype V]
        [Fintype Copy] [Fintype I] [Fintype B] [LinearOrder B],
      ∀ (Lyt : SourceLayout E V F Copy I B) (tm tg : I) (g : B) (q T R : ℕ)
        (omitted : Finset ℕ) (_P : SourceVisits (fun j=>j∉omitted) Lyt tm tg g q T),
      n₀≤Fintype.card V →
      (Fintype.card E:ℝ)≤(Fintype.card V:ℝ)*(logTwo (Fintype.card V:ℝ))^β →
      2≤Fintype.card B → 1≤R → R<Fintype.card I → omitted.card≤R →
      (∀ u,cellLoad Lyt u * Fintype.card (WordCell I B)≤2*Fintype.card E) →
      ⌊κ*(Fintype.card V:ℝ)*(R:ℝ)/(Fintype.card I:ℝ)⌋₊≤q →
      c*(Fintype.card V:ℝ)*targetScale (logTwo (Fintype.card V:ℝ))
        (logTwo (logTwo (Fintype.card V:ℝ)))≤logTwo T := by
  let δ := min (κ/32) 1
  have hδ : 0<δ := lt_min (by positivity) (by norm_num)
  let γ := min 1 (δ/(8*log 2))
  have hlog2 : 0<log 2 := log_pos (by norm_num)
  have hγ : 0<γ := lt_min (by norm_num) (by positivity)
  let cutoff := nativeCutoff β
  have hc : 0<cutoff := (by norm_num : (0:ℝ)<256).trans_le (nativeCutoff_ge β hβ)
  have hM := eventual_density_margins β hβ
  have hE := eventual_scale_margins κ δ cutoff hκ hδ hc
  have hlogn := (tendsto_log_atTop.comp tendsto_log_atTop).eventually (eventually_ge_atTop (1:ℝ))
  have hAll := (eventually_ge_atTop (2:ℝ)).and (hlogn.and (hM.and hE))
  obtain ⟨x₀,hx₀⟩ := eventually_atTop.mp hAll
  let n₀ := ⌈max 2 x₀⌉₊
  refine ⟨γ/fromNaturalLogScale,div_pos hγ fromNaturalLogScale_pos,n₀,?_⟩
  intro E V F Copy I B _ _ _ _ _ _ Lyt tm tg g q T R omitted P hn hM' hr hR hRQ hOmit hcap horder
  let n := Fintype.card V
  have hx : x₀≤(n:ℝ) := (le_max_right _ _).trans ((Nat.le_ceil _).trans (by exact_mod_cast hn))
  obtain ⟨hN,hll,H,⟨S⟩⟩ := hx₀ (n:ℝ) hx
  letI : Nonempty E := by
    have hv : 0<Fintype.card V := by exact_mod_cast (show 0<(n:ℝ) by linarith only [hN])
    obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp hv
    obtain ⟨e,_⟩ := Lyt.placement.occurs v
    exact ⟨e⟩
  have hMp : 0<(Fintype.card E:ℝ) := by exact_mod_cast (Fintype.card_pos : 0<Fintype.card E)
  obtain ⟨hlM,hMdense⟩ := H (Fintype.card E:ℝ) hMp hM'
  have hBnd := finite_FA4 Lyt tm tg g q T R (log (n:ℝ)) (log (log (n:ℝ))) κ δ cutoff
    omitted hOmit P hr hR (by omega : 0<Fintype.card I) hcap
    S.Lpos S.lpos hκ hδ (min_le_left _ _) (min_le_right _ _) hc horder hlM
    S.alphaCost S.alphaOne S.cutoffSmall S.widthSmall S.alphaDecay S.widthDecay S.choiceLarge S.threshold
    (by intro h; exact hMdense _ h)
  have hScale := scale_compare_binary (n:ℝ) (by linarith only [hN]) hll
  have hfactor := mul_le_mul_of_nonneg_left hScale
    (mul_nonneg (div_nonneg hγ.le fromNaturalLogScale_pos.le) (by positivity : 0≤(n:ℝ)))
  refine hfactor.trans ?_
  have hh : (γ/fromNaturalLogScale)*(n:ℝ)*
      (fromNaturalLogScale*targetScale (log (n:ℝ)) (log (log (n:ℝ)))) =
        γ*((n:ℝ)*targetScale (log (n:ℝ)) (log (log (n:ℝ)))) := by
    field_simp [fromNaturalLogScale_pos.ne']
  rw [hh]
  exact hBnd

#print axioms scale_compare_binary
#print axioms eventual_FA4
end P5MainIterator
