import P5HybridMultiMoment

/-! The given eta-balanced symbol unions are never changed. Their
arbitrary dependent family is submitted to one existing common
matching experiment. -/
namespace Paper5.HybridMulti
open scoped BigOperators Classical
open Paper5.HybridClosure GraphCutMoments EmpiricalCutMoments CommonMatchingSelection SeparatedRank

theorem law_constant_ge_one {V X : Type*} [Fintype V] [Nonempty V] [Fintype X]
    [DecidableEq X] [Nonempty X] (L : V→X) (C : ℚ)
    (h : ∀ x,empiricalLaw L x≤C*ProductVariance.uniformWeight X) : 1≤C := by
  have hX : (Fintype.card X:ℚ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hU : (∑ _x : X,ProductVariance.uniformWeight X)=1 := by
    simp only [ProductVariance.uniformWeight,Finset.sum_const,nsmul_eq_mul,
      Finset.card_univ,mul_inv_cancel₀ hX]
  have hh := Finset.sum_le_sum (fun x (h' : x∈(Finset.univ : Finset X))=>h x)
  rw [sum_empiricalLaw,←Finset.mul_sum,hU,mul_one] at hh
  exact hh

noncomputable def boundaryDensity (γ η : ℚ) : ℚ := 2*γ*η/3

noncomputable def familyMargin (V : Type*) [Fintype V] (γ η H w : ℚ) : ℚ :=
  rate 36*(9*(boundaryDensity γ η)^2*(Fintype.card V:ℚ)*w/(128*H))

section Family
variable {V S : Type*} {I A : S→Type*}
  [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype S] [Nonempty S]
  [∀ s,Fintype (I s)] [∀ s,DecidableEq (I s)] [∀ s,Nonempty (I s)]
  [∀ s,Fintype (A s)] [∀ s,DecidableEq (A s)] [∀ s,Nonempty (A s)]

set_option maxHeartbeats 12000000 in
theorem arbitrary_family_common_matching_exact
    (E : Finset (V×V)) (hloop : ∀ v,(v,v)∉E) (hreg : ∀v,degree E v=3)
    (L : ∀ s,V→I s→A s) (symbols : ∀ s,I s→Finset (A s))
    (C w H : S→ℚ) (γ η : ℚ) (hγ : 0<γ) (hγ1 : γ≤1) (hη : 0<η) (hη1 : η≤1/2)
    (hExp : ∀ U : Finset V,γ*(min U.card (Fintype.card V-U.card):ℕ)≤
      ((boundary E U).card:ℚ))
    (hBalance : ∀ s i,η*(Fintype.card V:ℚ)≤
      (min (labelCut (L s) id (symbols s) i).card
        (Fintype.card V-(labelCut (L s) id (symbols s) i).card):ℕ))
    (hDom : ∀ s x,empiricalLaw (L s) x≤C s*ProductVariance.uniformWeight (I s→A s))
    (hW : ∀ s,0<w s) (hH : ∀ s,0≤H s)
    (hNorm : ∀ s,(w s)^2*C s*(Fintype.card (I s):ℚ)≤(H s)^2)
    (d : S→ℕ) (hd : ∀ s,(d s:ℚ)≤familyMargin V γ η (∑ s,H s) (w s))
    (hBudget : (∑ s,(Fintype.card (I s):ℚ)*(7776*(Fintype.card V:ℚ))/
      (familyMargin V γ η (∑ s,H s) (w s))^2)<1) :
    ∃ mark orientation : E→Bool,∀ s i,
      d s≤endpointImbalance (MatchingThinning.matching E hloop mark orientation).endpoint
        (labelCut (L s) id (symbols s) i) := by
  let Z : ℚ := ∑ s,H s
  let p := boundaryDensity γ η
  let cuts := combinedCuts L symbols
  have hC (s : S) : 1≤C s := law_constant_ge_one (L s) (C s) (hDom s)
  have hWpart (s : S) : w s≤H s := by
    have hI : (1:ℚ)≤Fintype.card (I s) := by
      exact_mod_cast (Fintype.card_pos (α:=I s))
    apply (sq_le_sq₀ (hW s).le (hH s)).mp
    calc
      _ ≤ (w s)^2*C s*(Fintype.card (I s):ℚ) := by
        calc
          _ = ((w s)^2*1)*1 := by ring
          _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left (hC s) (sq_nonneg _)) hI
            (by norm_num) (mul_nonneg (sq_nonneg _) (by linarith only [hC s]))
      _ ≤ _ := hNorm s
  have hWtot (s : S) : w s≤Z := (hWpart s).trans (Finset.single_le_sum
    (fun u _=>hH u) (Finset.mem_univ s))
  have hZ : 0<Z := (hW (Classical.choice inferInstance)).trans_le (hWtot _)
  have hV : 0<(Fintype.card V:ℚ) := by exact_mod_cast (Fintype.card_pos (α:=V))
  have hE : 2*(E.card:ℚ)=3*(Fintype.card V:ℚ) := by exact_mod_cast regular_edge_count E 3 hreg
  have hEpos : 0<(E.card:ℚ) := by linarith only [hE,hV]
  have hp : 0<p := by dsimp [p,boundaryDensity]; positivity
  have hp1 : p≤1 := by
    have h := mul_le_mul hγ1 hη1 hη.le (by norm_num : (0:ℚ)≤1)
    unfold p boundaryDensity
    linarith only [h]
  have hbnd (j : Σ s,I s) : p≤((boundary E (cuts j)).card:ℚ)/E.card := by
    apply (le_div_iff₀ hEpos).2
    calc
      _ = γ*(η*(Fintype.card V:ℚ)) := by
        unfold p boundaryDensity
        have := congrArg (fun x:ℚ => (γ*η/3)*x) hE
        nlinarith only [this]
      _ ≤ _ := (mul_le_mul_of_nonneg_left (hBalance j.1 j.2) hγ.le).trans (hExp (cuts j))
  have hm (s : S) :
      rate 36*(3*p^2*(E.card:ℚ)*w s/(64*Z)) = familyMargin V γ η Z (w s) := by
    have he : (E.card:ℚ)=3*(Fintype.card V:ℚ)/2 := by linarith only [hE]
    rw [he]
    unfold familyMargin
    change _ = rate 36*(9*p^2*(Fintype.card V:ℚ)*w s/(128*Z))
    ring
  have hVariance : 4*(E.card:ℚ)*1296=7776*(Fintype.card V:ℚ) := by linarith only [hE]
  have hbudget' : (∑ j : Σ s,I s,(4*(E.card:ℚ)*1296)/
      (rate 36*(3*p^2*(E.card:ℚ)*w j.1/(64*Z)))^2)<1 := by
    simp_rw [hm,hVariance]
    rw [Fintype.sum_sigma]
    simpa only [Finset.sum_const,nsmul_eq_mul,Finset.card_univ,mul_div_assoc] using hBudget
  obtain ⟨mark,orientation,h⟩ :=
    weighted_cubic_cut_matching E hloop hreg cuts (fun j=>cutDensity (cuts j)) (fun j=>w j.1)
      p Z hp hp1 hZ (fun j=>hW j.1) (fun j=>hWtot j.1) hbnd
      (weighted_multi_layout_moment L symbols C w H (fun s=>(hC s).trans' zero_le_one)
        hH hDom hNorm) (fun j=>d j.1) (fun j=>by rw [hm]; exact hd j.1) hbudget'
  exact ⟨mark,orientation,fun s i=>h ⟨s,i⟩⟩

end Family

#print axioms law_constant_ge_one
#print axioms arbitrary_family_common_matching_exact
end Paper5.HybridMulti
