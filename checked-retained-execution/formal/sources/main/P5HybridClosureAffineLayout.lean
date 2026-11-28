import P5HybridClosureJoin
import P5HybridClosureRates

/-! Finite, route-specific affine lower bound with the manuscript's
scaling, on the actual cloned input.  The layout laws are supplied by
the graph-only split-placement theorem. -/
namespace Paper5.HybridClosure
open scoped BigOperators Classical
open GraphCutMoments EmpiricalCutMoments CommonMatchingSelection GroupProducts SeparatedRank

variable {V IM ID AM AD TM TD R S K : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype IM] [DecidableEq IM] [Nonempty IM] [Fintype ID] [DecidableEq ID] [Nonempty ID]
  [Fintype AM] [DecidableEq AM] [Nonempty AM]
  [Fintype AD] [DecidableEq AD] [Nonempty AD]
  [Fintype TM] [Fintype TD] [CommRing R] [CommRing S] [Nontrivial S] [Field K]

set_option maxHeartbeats 5000000 in
theorem fixed_affine_after_layout_choice (F : Finset (V×V))
    (hloop : ∀v,(v,v)∉F) (hreg : ∀v,degree F v=3)
    (L_M : V→IM→AM) (L_D : V→ID→AD) (γ : ℚ)
    (hγ : 0<γ) (hγ1 : γ≤1)
    (hE : ∀ U : Finset V, γ*(min U.card (Fintype.card V-U.card):ℕ)≤
      ((boundary F U).card:ℚ))
    (hdomM : ∀x,empiricalLaw L_M x≤24*ProductVariance.uniformWeight (IM→AM))
    (hdomD : ∀x,empiricalLaw L_D x≤48*ProductVariance.uniformWeight (ID→AD))
    (hrM : 32≤Fintype.card AM) (hrD : 64≤Fintype.card AD)
    (hbudget : 31104*((Fintype.card IM:ℚ)^2+(Fintype.card ID:ℚ)^2)<
      (matchingCoeff γ)^2*(Fintype.card V:ℚ)) :
    let dM := routeDepth γ (Fintype.card V) (Fintype.card IM)
    let dD := routeDepth γ (Fintype.card V) (Fintype.card ID)
    ∃ (s_M : IM→Finset AM) (s_D : ID→Finset AD) (mark orientation : F→Bool),
      let matching := MatchingThinning.matching F hloop mark orientation
      (∀j,dM≤endpointImbalance matching.endpoint (labelCut L_M id s_M j)) ∧
      (∀j,dD≤endpointImbalance matching.endpoint (labelCut L_D id s_D j)) ∧
      ∀ (terms_M : TM→GroupTerm L_M K) (terms_D : TD→GroupTerm L_D K)
        (embed : R→+*K) (residue : R→+*S) (_hinj : Function.Injective embed)
        (output : (V→Bool)→R),
      (∀σ,embed (output σ)=(∑t,(terms_M t).value σ)+∑t,(terms_D t).value σ) →
      (∀σ,residue (output σ)=(PinnedCNF.modelCount
        (MainClonedCNF.formula F (MainClonedCNF.leftSlot F hreg) (MainClonedCNF.rightSlot F hreg) σ):S)) →
      ((1:ℚ)≤(Fintype.card TM:ℚ)/(2:ℚ)^dM+(Fintype.card TD:ℚ)/(2:ℚ)^dD) ∧
          2^(min dM dD)≤Fintype.card TM+Fintype.card TD := by
  let dM := routeDepth γ (Fintype.card V) (Fintype.card IM)
  let dD := routeDepth γ (Fintype.card V) (Fintype.card ID)
  let wM := routeWeight (Fintype.card IM)
  let wD := routeWeight (Fintype.card ID)
  have hMweight : wM^2*24*(Fintype.card IM:ℚ)≤(5:ℚ)^2 := by
    have h := mul_le_mul_of_nonneg_left (routeWeight_square_scale (Fintype.card IM))
      (by decide : (0:ℚ)≤24)
    nlinarith only [h]
  have hDweight : wD^2*48*(Fintype.card ID:ℚ)≤(7:ℚ)^2 := by
    have h := mul_le_mul_of_nonneg_left (routeWeight_square_scale (Fintype.card ID))
      (by decide : (0:ℚ)≤48)
    nlinarith only [h]
  have hrM' : (32:ℚ)≤Fintype.card AM := by exact_mod_cast hrM
  have hrD' : (64:ℚ)≤Fintype.card AD := by exact_mod_cast hrD
  have huM : (24:ℚ)/(Fintype.card AM:ℚ)≤3/4 := by
    apply (div_le_iff₀ (by positivity : (0:ℚ)<Fintype.card AM)).2
    linarith only [hrM']
  have huD : (48:ℚ)/(Fintype.card AD:ℚ)≤3/4 := by
    apply (div_le_iff₀ (by positivity : (0:ℚ)<Fintype.card AD)).2
    linarith only [hrD']
  have hF := regular_edge_count F 3 hreg
  have hFvariance : 4*(F.card:ℚ)*1296=7776*(Fintype.card V:ℚ) := by
    have h : 2*(F.card:ℚ)=3*(Fintype.card V:ℚ) := by exact_mod_cast hF
    linarith only [h]
  have hNorm (k : ℕ) : LayoutResult F (routeWeight k) (5+7) (γ/6) =
      matchingCoeff γ*(Fintype.card V:ℚ)*routeWeight k :=
    by simpa [LayoutResult,show (5+7:ℚ)=12 by norm_num] using normalized_matching_margin F hF γ k
  have hdM : (dM:ℚ)≤LayoutResult F wM (5+7) (γ/6) := by
    rw [hNorm]
    exact (routeDepth_margin γ hγ _ _).1
  have hdD : (dD:ℚ)≤LayoutResult F wD (5+7) (γ/6) := by
    rw [hNorm]
    exact (routeDepth_margin γ hγ _ _).1
  have hBudget : (Fintype.card IM:ℚ)*(4*(F.card:ℚ)*1296)/
      (LayoutResult F wM (5+7) (γ/6))^2+
      (Fintype.card ID:ℚ)*(4*(F.card:ℚ)*1296)/
      (LayoutResult F wD (5+7) (γ/6))^2<1 := by
    rw [hNorm,hNorm,hFvariance]
    exact two_route_union_test _ (matchingCoeff_pos γ hγ) _ _ _ Fintype.card_pos
      Fintype.card_pos Fintype.card_pos hbudget
  have hwM : wM≤(5:ℚ)+7 := (routeWeight_le_one _).trans (by norm_num)
  have hwD : wD≤(5:ℚ)+7 := (routeWeight_le_one _).trans (by norm_num)
  obtain ⟨s_M,s_D,mark,orientation,hM,hD⟩ := same_matching_for_two_layouts F hloop hreg
    L_M L_D 24 48 wM wD 5 7 γ (by decide) (by decide) (by decide) (by decide)
    (routeWeight_pos _) (routeWeight_pos _) hwM hwD hγ hγ1 hE hdomM hdomD huM huD
    hMweight hDweight dM dD hdM hdD hBudget
  refine ⟨s_M,s_D,mark,orientation,hM,hD,?_⟩
  intro tM tD embed residue hinj output repr hcorrect
  let matching := MatchingThinning.matching F hloop mark orientation
  have nd := cloned_fixed_mixed_affine_residue F _ _ matching L_M L_D s_M s_D tM tD dM dD
    ((hM (Classical.choice inferInstance)).trans (endpoint_imbalance_le _ _))
    ((hD (Classical.choice inferInstance)).trans (endpoint_imbalance_le _ _))
    hM hD embed residue hinj output repr hcorrect
  exact ⟨nd,minimum_depth_term_count (min_le_left _ _) (min_le_right _ _) nd⟩

#print axioms fixed_affine_after_layout_choice
end Paper5.HybridClosure