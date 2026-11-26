import P5HybridMultiMatching
import P5HybridMultiBudget
import P5HybridMultiApprox

/-! Paper 5 §5.2, Theorem 1 (X1): the prescribed symbol
unions, heterogeneous real weights, and the original strict
normalized budget. The argument admits arbitrary correlation
between different layouts. -/
namespace Paper5.HybridMulti
open scoped BigOperators Classical
open Paper5.HybridClosure GraphCutMoments EmpiricalCutMoments
  CommonMatchingSelection SeparatedRank

theorem real_law_constant_ge_one {V X : Type*} [Fintype V] [Nonempty V]
    [Fintype X] [DecidableEq X] [Nonempty X] (L : V→X) (C : ℝ)
    (h : ∀ x,(empiricalLaw L x:ℝ)≤C*(ProductVariance.uniformWeight X:ℝ)) : 1≤C := by
  have hX : (Fintype.card X:ℚ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hU : (∑ _x : X,ProductVariance.uniformWeight X)=1 := by
    simp only [ProductVariance.uniformWeight,Finset.sum_const,nsmul_eq_mul,
      Finset.card_univ,mul_inv_cancel₀ hX]
  have hUR : (∑ _x : X,(ProductVariance.uniformWeight X:ℝ))=1 := by
    exact_mod_cast hU
  have hMass : (∑ x : X,(empiricalLaw L x:ℝ))=1 := by
    exact_mod_cast (sum_empiricalLaw L)
  have hh := Finset.sum_le_sum (fun x (h' : x∈(Finset.univ : Finset X))=>h x)
  rw [hMass,←Finset.mul_sum,hUR,mul_one] at hh
  exact hh

theorem margin_scalar (V : Type*) [Fintype V] (γ η Z v : ℚ) :
    (familyMargin V γ η Z v:ℝ) =
      ((rate 36*(9*(boundaryDensity γ η)^2/128):ℚ):ℝ) *
        (Fintype.card V:ℝ)*(v:ℝ)/(Z:ℝ) := by
  have h : familyMargin V γ η Z v =
      (rate 36*(9*(boundaryDensity γ η)^2/128))*(Fintype.card V:ℚ)*v/Z := by
    unfold familyMargin
    ring
  exact_mod_cast h

universe u v x y
set_option maxHeartbeats 22000000 in
theorem x1_arbitrary_layouts (γ η : ℝ) (hγ : 0<γ) (hη : 0<η) (hη1 : η≤1/2) :
    ∃ a B : ℝ,0<a ∧ 0<B ∧
      ∀ {V : Type u} {S : Type v} {I : S→Type x} {A : S→Type y}
      [Fintype V] [DecidableEq V] [Nonempty V] [Fintype S]
      [∀ s,Fintype (I s)] [∀ s,DecidableEq (I s)] [∀ s,Nonempty (I s)]
      [∀ s,Fintype (A s)] [∀ s,DecidableEq (A s)] [∀ s,Nonempty (A s)],
      ∀ (E : Finset (V×V)) (hloop : ∀ v,(v,v)∉E),
      (∀ v,degree E v=3) →
      ∀ (L : ∀ s,V→I s→A s) (symbols : ∀ s,I s→Finset (A s)) (C w : S→ℝ),
      (∀ U : Finset V,γ*(min U.card (Fintype.card V-U.card):ℕ)≤
        ((boundary E U).card:ℝ)) →
      (∀ s i,η*(Fintype.card V:ℝ)≤
        (min (labelCut (L s) id (symbols s) i).card
          (Fintype.card V-(labelCut (L s) id (symbols s) i).card):ℕ)) →
      (∀ s z,(empiricalLaw (L s) z:ℝ)≤C s*(ProductVariance.uniformWeight (I s→A s):ℝ)) →
      (∀ s,0<w s) →
      (let H := combinedScale C w (fun s=>Fintype.card (I s))
       B*(H^2/(Fintype.card V:ℝ))*(∑s,(Fintype.card (I s):ℝ)/(w s)^2)<1) →
      ∃ mark orientation : E→Bool,∀ s i,
        a*(Fintype.card V:ℝ)*w s/(combinedScale C w (fun s=>Fintype.card (I s)))≤
          (endpointImbalance (MatchingThinning.matching E hloop mark orientation).endpoint
            (labelCut (L s) id (symbols s) i):ℝ) := by
  obtain ⟨g,hg0,hgu⟩ := exists_rat_btwn (lt_min hγ (by norm_num : (0:ℝ)<1))
  obtain ⟨e,he0,heu⟩ := exists_rat_btwn hη
  have hgq : 0<g := by exact_mod_cast hg0
  have heq : 0<e := by exact_mod_cast he0
  have hg1 : g≤1 := by exact_mod_cast ((lt_min_iff.mp hgu).2.le)
  have he1 : e≤1/2 := by
    apply (Rat.cast_le (K:=ℝ)).mp
    push_cast
    exact heu.le.trans hη1
  let K : ℝ := ((rate 36*(9*(boundaryDensity g e)^2/128):ℚ):ℝ)
  have hK : 0<K := by
    have hp : 0<boundaryDensity g e := by dsimp [boundaryDensity]; positivity
    change (0:ℝ)<((rate 36*(9*(boundaryDensity g e)^2/128):ℚ):ℝ)
    exact_mod_cast (mul_pos (rate_pos 36) (by positivity : (0:ℚ)<9*(boundaryDensity g e)^2/128))
  refine ⟨K/12,36*7776/K^2,by positivity,by positivity,?_⟩
  intro V S I A vF vD vN sF iF iD iN aF aD aN E hloop hreg L symbols C w hExp hBal hDom hw hBudget
  by_cases hS : Nonempty S
  swap
  · letI : IsEmpty S := ⟨fun s=>hS ⟨s⟩⟩
    exact ⟨fun _=>false,fun _=>false,fun s=>isEmptyElim s⟩
  letI : Nonempty S := hS
  let k (s : S) := Fintype.card (I s)
  let N := Fintype.card V
  let H := combinedScale C w k
  have hN : 0<N := Fintype.card_pos
  have hNR : (0:ℝ)<N := by exact_mod_cast hN
  have hk (s : S) : 0<k s := Fintype.card_pos
  have hC (s : S) : 1≤C s := real_law_constant_ge_one (L s) (C s) (hDom s)
  have hH : 0<H := combinedScale_positive C w k hC hw hk
  obtain ⟨D⟩ := exists_approximation C w k hC hw hk
  let Z : ℚ := ∑s,D.hq s
  have hZ : 0<Z :=
    (D.positive (Classical.choice inferInstance)).trans_le
      (Finset.single_le_sum (fun s _=>(D.positive s).le) (Finset.mem_univ _))
  have hZR : (0:ℝ)<(Z:ℝ) := by exact_mod_cast hZ
  have hZA : (Z:ℝ)≤3*H := by
    change (((∑s,D.hq s):ℚ):ℝ)≤3*combinedScale C w k
    simpa only [Rat.cast_sum] using D.sum
  have hwR (s : S) : (0:ℝ)<(D.wq s:ℝ) := (by linarith only [hw s] : 0<w s/2).trans_le (D.weights s)
  have hwQ (s : S) : (0:ℚ)<D.wq s := by exact_mod_cast hwR s
  have hExpQ (U : Finset V) : g*(min U.card (Fintype.card V-U.card):ℕ)≤
      ((boundary E U).card:ℚ) := by
    have h : (g:ℝ)*(min U.card (Fintype.card V-U.card):ℕ)≤
        ((boundary E U).card:ℝ) :=
      (mul_le_mul_of_nonneg_right ((lt_min_iff.mp hgu).1.le) (by positivity)).trans (hExp U)
    exact_mod_cast h
  have hBalQ (s : S) (i : I s) :
      e*(Fintype.card V:ℚ)≤(min (labelCut (L s) id (symbols s) i).card
        (Fintype.card V-(labelCut (L s) id (symbols s) i).card):ℕ) := by
    have h : (e:ℝ)*(Fintype.card V:ℝ)≤(min (labelCut (L s) id (symbols s) i).card
        (Fintype.card V-(labelCut (L s) id (symbols s) i).card):ℕ) :=
      (mul_le_mul_of_nonneg_right heu.le (by positivity)).trans (hBal s i)
    exact_mod_cast h
  have hDomQ (s : S) (z : I s→A s) :
      empiricalLaw (L s) z≤D.cq s*ProductVariance.uniformWeight (I s→A s) := by
    have hU : (0:ℚ)≤ProductVariance.uniformWeight (I s→A s) := by
      unfold ProductVariance.uniformWeight
      positivity
    have hUR : (0:ℝ)≤(ProductVariance.uniformWeight (I s→A s):ℝ) := by exact_mod_cast hU
    have h : (empiricalLaw (L s) z:ℝ)≤(D.cq s:ℝ)*(ProductVariance.uniformWeight (I s→A s):ℝ) :=
      (hDom s z).trans (mul_le_mul_of_nonneg_right (D.dom s) hUR)
    exact_mod_cast h
  let m (s : S) : ℝ := (familyMargin V g e Z (D.wq s):ℝ)
  have hm (s : S) : K*(N:ℝ)*w s/(6*H)≤m s := by
    rw [show m s=(familyMargin V g e Z (D.wq s):ℝ) from rfl,margin_scalar]
    exact compare_rounded_margin K (N:ℝ) H (Z:ℝ) (w s) (D.wq s:ℝ)
      hK hNR hH hZR (hwR s) (D.weights s) hZA
  change (36*7776/K^2)*(H^2/(N:ℝ))*(∑s,(k s:ℝ)/(w s)^2)<1 at hBudget
  obtain ⟨hUnion,hCeils⟩ := normalized_budget_and_ceils N hN k hk K H hK hH w m hw hm hBudget
  let d (s : S) := ⌈K*(N:ℝ)*w s/(12*H)⌉₊
  have hd (s : S) : (d s:ℚ)≤familyMargin V g e Z (D.wq s) := by
    have h : (d s:ℝ)≤(familyMargin V g e Z (D.wq s):ℝ) := hCeils s
    exact_mod_cast h
  have hUnionQ : (∑s,(k s:ℚ)*(7776*(N:ℚ))/(familyMargin V g e Z (D.wq s))^2)<1 := by
    have h : (∑s,(k s:ℝ)*(7776*(N:ℝ))/((familyMargin V g e Z (D.wq s):ℚ):ℝ)^2)<1 := hUnion
    exact_mod_cast h
  obtain ⟨mark,orient,hLarge⟩ := arbitrary_family_common_matching_exact E hloop hreg L symbols
    D.cq D.wq D.hq g e hgq hg1 heq he1 hExpQ hBalQ hDomQ hwQ
      (fun s=>(D.positive s).le) D.norm d hd hUnionQ
  refine ⟨mark,orient,fun s i=>?_⟩
  change (K/12)*(N:ℝ)*w s/H≤_
  calc
    _ = K*(N:ℝ)*w s/(12*H) := by ring
    _ ≤ (d s:ℝ) := Nat.le_ceil _
    _ ≤ _ := by exact_mod_cast (hLarge s i)

#print axioms real_law_constant_ge_one
#print axioms margin_scalar
#print axioms x1_arbitrary_layouts
end Paper5.HybridMulti
