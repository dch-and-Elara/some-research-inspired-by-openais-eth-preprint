import P5HybridClosureMoment
import P5HybridClosureDensity

/-! The single weighted orientation is fixed from the two selected layouts
before the terms, scalar coefficients, or program are chosen.  The
finite inequality retains the two different deficits. -/
namespace Paper5.HybridClosure
open scoped BigOperators Classical
open GraphCutMoments EmpiricalCutMoments CommonMatchingSelection GroupProducts SeparatedRank

section Endpoint
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq I] in
theorem endpoint_imbalance_le (e : (I×Bool)↪V) (T : Finset V) :
    endpointImbalance e T≤Fintype.card I := by
  dsimp [endpointImbalance]
  have h₁ := Finset.card_le_univ (endpointPart e T false)
  have h₂ := Finset.card_le_univ (endpointPart e T true)
  omega
end Endpoint

section Layouts
variable {V IM ID AM AD : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype IM] [DecidableEq IM] [Nonempty IM] [Fintype ID] [DecidableEq ID] [Nonempty ID]
  [Fintype AM] [DecidableEq AM] [Nonempty AM]
  [Fintype AD] [DecidableEq AD] [Nonempty AD]

abbrev LayoutResult (F : Finset (V×V)) (w H p : ℚ) :=
  rate 36*(3*p^2*(F.card:ℚ)*w/(64*H))

set_option maxHeartbeats 1500000 in
omit [Nonempty IM] [Nonempty ID] in
theorem same_matching_for_two_layouts (F : Finset (V×V))
    (hloop : ∀v,(v,v)∉F) (hreg : ∀v,degree F v=3)
    (L_M : V→IM→AM) (L_D : V→ID→AD)
    (C_M C_D wM wD H_M H_D γ : ℚ)
    (hCM : 0≤C_M) (hCD : 0≤C_D) (hHM : 0≤H_M) (hHD : 0≤H_D)
    (hwM : 0<wM) (hwD : 0<wD) (hM_H : wM≤H_M+H_D) (hD_H : wD≤H_M+H_D)
    (hγ : 0<γ) (hγ1 : γ≤1)
    (hE : ∀ U : Finset V, γ*(min U.card (Fintype.card V-U.card):ℕ)≤
      ((boundary F U).card:ℚ))
    (hdomM : ∀x,empiricalLaw L_M x≤C_M*ProductVariance.uniformWeight (IM→AM))
    (hdomD : ∀x,empiricalLaw L_D x≤C_D*ProductVariance.uniformWeight (ID→AD))
    (hsymM : C_M/(Fintype.card AM:ℚ)≤3/4) (hsymD : C_D/(Fintype.card AD:ℚ)≤3/4)
    (hM : wM^2*C_M*(Fintype.card IM:ℚ)≤H_M^2)
    (hD : wD^2*C_D*(Fintype.card ID:ℚ)≤H_D^2)
    (dM dD : ℕ)
    (hdM : (dM:ℚ)≤LayoutResult F wM (H_M+H_D) (γ/6))
    (hdD : (dD:ℚ)≤LayoutResult F wD (H_M+H_D) (γ/6))
    (hbudget : (Fintype.card IM:ℚ)*(4*(F.card:ℚ)*1296)/
      (LayoutResult F wM (H_M+H_D) (γ/6))^2+
      (Fintype.card ID:ℚ)*(4*(F.card:ℚ)*1296)/
      (LayoutResult F wD (H_M+H_D) (γ/6))^2<1) :
    ∃ (s_M : IM→Finset AM) (s_D : ID→Finset AD) (mark orientation : F→Bool),
      let M := MatchingThinning.matching F hloop mark orientation
      (∀ j,dM≤endpointImbalance M.endpoint (labelCut L_M id s_M j)) ∧
      (∀ j,dD≤endpointImbalance M.endpoint (labelCut L_D id s_D j)) := by
  have hH : 0<H_M+H_D := hwM.trans_le hM_H
  let p := γ/6
  obtain ⟨s_M,bal_M⟩ := choose_balanced_symbols L_M C_M hdomM hsymM
  obtain ⟨s_D,bal_D⟩ := choose_balanced_symbols L_D C_D hdomD hsymD
  let cuts := pairedCuts L_M L_D s_M s_D
  let w : IM⊕ID→ℚ := pairedWeights wM wD
  let d : IM⊕ID→ℕ := Sum.elim (fun _=>dM) (fun _=>dD)
  have hbal : ∀ j,(1/4:ℚ)*Fintype.card V≤
      (min (cuts j).card (Fintype.card V-(cuts j).card):ℕ) := by
    intro j
    cases j with
    | inl j => exact bal_M j
    | inr j => exact bal_D j
  have hF : 2*(F.card:ℚ)=3*(Fintype.card V:ℚ) := by exact_mod_cast regular_edge_count F 3 hreg
  have hFpos : 0<(F.card:ℚ) := by
    have hv : 0<(Fintype.card V:ℚ) := by exact_mod_cast (Fintype.card_pos (α:=V))
    linarith only [hF,hv]
  have hbnd (j : IM⊕ID) : p≤((boundary F (cuts j)).card:ℚ)/F.card := by
    apply (le_div_iff₀ hFpos).2
    calc
      _ = γ*((1/4:ℚ)*Fintype.card V) := by
        have h := congrArg (fun a : ℚ => (γ/12)*a) hF
        dsimp [p]
        nlinarith only [h]
      _ ≤ _ := (mul_le_mul_of_nonneg_left (hbal j) hγ.le).trans (hE (cuts j))
  have hw (j : IM⊕ID) : 0<w j := by cases j; exact hwM; exact hwD
  have hW (j : IM⊕ID) : w j≤H_M+H_D := by cases j; exact hM_H; exact hD_H
  have hdepth (j : IM⊕ID) : (d j:ℚ)≤LayoutResult F (w j) (H_M+H_D) p := by
    cases j
    · exact hdM
    · exact hdD
  have hb : (∑j, (4*(F.card:ℚ)*1296)/(LayoutResult F (w j) (H_M+H_D) p)^2)<1 := by
    rw [Fintype.sum_sum_type]
    simpa [w,pairedWeights,p,nsmul_eq_mul,mul_div_assoc] using hbudget
  have hp : 0<p := by dsimp [p]; positivity
  have hp1 : p≤1 := by dsimp [p]; linarith only [hγ1]
  obtain ⟨mark,orientation,common⟩ := weighted_cubic_cut_matching F hloop hreg cuts
    (fun j=>cutDensity (cuts j)) w p (H_M+H_D) hp hp1 hH hw hW hbnd
    (weighted_two_route_moment L_M L_D s_M s_D C_M C_D wM wD H_M H_D hCM hCD hHM hHD
      hdomM hdomD hM hD) d hdepth hb
  exact ⟨s_M,s_D,mark,orientation,(fun j=>common (.inl j)),(fun j=>common (.inr j))⟩
end Layouts

#print axioms endpoint_imbalance_le
#print axioms same_matching_for_two_layouts
end Paper5.HybridClosure