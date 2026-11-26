import P5HybridClosureExpand
import CommonMatchingSelection
import WeightedHybrid

/-! Heterogeneous margins in the one-common-matching thinning of §5/§8.
Events on different source layouts may be arbitrarily correlated; only
the graph-local auxiliary coin experiment is independent. -/
namespace Paper5.HybridClosure
open scoped BigOperators Classical
open CommonMatchingSelection GraphCutMoments

variable {V J : Type*} [Fintype V] [DecidableEq V] [Fintype J]

omit [Fintype V] in
theorem select_weighted_matching (E : Finset (V×V)) (hloop : ∀v,(v,v)∉E)
    (B : ℕ) (hblock : ∀ e, (MatchingThinning.block E e).card≤B)
    (cuts : J→Finset V) (b : E→ℚ) (hb : ∀e, |b e|≤1)
    (margin : J→ℚ) (d : J→ℕ) (hmargin : ∀j,0<margin j) (hd : ∀j,(d j:ℚ)≤margin j)
    (hmean : ∀j,2*margin j≤rate B*|∑e : E,b e*cutDifference ℚ (cuts j) e.1|)
    (hbudget : (∑ j, (4*(E.card:ℚ)*(B*B:ℕ))/margin j^2)<1) :
    ∃ mark orientation : E→Bool, ∀j,
      d j≤SeparatedRank.endpointImbalance
        (MatchingThinning.matching E hloop mark orientation).endpoint (cuts j) := by
  let blocks := MatchingThinning.block E
  let w := bias B blocks b
  let μ := IndependentThinning.prob w
  let Z := fun e (ω : IndependentThinning.Outcome E) => IndependentThinning.signedValue blocks ω e
  let c := fun j (e : E) => cutDifference ℚ (cuts j) e.1
  let Y := fun j ω => ∑ e : E,c j e*Z e ω
  let a := fun j => rate B*∑ e : E,b e*c j e
  let variance : ℚ := 4*(E.card:ℚ)*(B*B:ℕ)
  have hμ : ∀ω,0≤μ ω := IndependentThinning.prob_nonneg w (bias_abs_le B blocks b hblock hb)
  have hmass : ∑ ω,μ ω=1 := IndependentThinning.sum_prob w
  have hfirst (e : E) : LocalVariance.mean μ (Z e)=rate B*b e :=
    (IndependentThinning.mean_signedValue w blocks e (MatchingThinning.self_mem_block E e)).trans
      (retention_bias B blocks b e)
  have hcenter (j : J) : (∑ e : E,c j e*LocalVariance.mean μ (Z e))=a j := by
    simp only [hfirst,a,Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by ring
  have hmom (j : J) : (∑ω,μ ω*(Y j ω-a j)^2)≤variance := by
    rw [←hcenter]
    have hv := LocalVariance.variance_of_disjoint_blocks μ Z (c j) blocks B hμ hmass
      (fun e ω => IndependentThinning.abs_signedValue_le_one blocks ω e)
      (fun e => abs_cutDifference_le_one (cuts j) e.1)
      (fun e f => (ThinningBlockBounds.mem_block_symm E e f).mp) hblock
      (fun e f hdis => IndependentThinning.disjoint_cross_moment w blocks e f
        (MatchingThinning.self_mem_block E e) (MatchingThinning.self_mem_block E f) hdis)
    simpa only [Fintype.card_coe] using hv
  have halarge (j : J) : 2*margin j≤|a j| := by
    simpa only [a,c,abs_mul,abs_of_nonneg (rate_pos B).le] using hmean j
  obtain ⟨ω,_,hall⟩ := FiniteSelection.exists_simultaneous_large μ Y a margin
    (fun _ => variance) hμ hmass hmargin hmom hbudget halarge
  refine ⟨fun e => (ω e).1,fun e => (ω e).2,?_⟩
  intro j
  apply (Nat.cast_le (α:=ℚ)).mp
  rw [realized_imbalance E hloop ω (cuts j)]
  exact (hd j).trans (hall j).le

set_option maxHeartbeats 2000000 in
/-- Finite common-matching result with original vertex cuts and arbitrary
positive per-cut weights. Unlike the manuscript's max-flow argument,
this proof obtains the same scaling directly from edge correlations. -/
theorem weighted_cubic_cut_matching [Nonempty V]
    (E : Finset (V×V)) (hloop : ∀v,(v,v)∉E) (hreg : ∀v,degree E v=3)
    (cuts : J→Finset V) (center : J→ℚ) (w : J→ℚ) (p H : ℚ)
    (hp : 0<p) (hp1 : p≤1) (hH : 0<H)
    (hw : ∀j,0<w j) (hwH : ∀j,w j≤H)
    (hbnd : ∀j,p≤((boundary E (cuts j)).card:ℚ)/E.card)
    (hmoment : ∀eps : J→Bool,
      (∑v,(BangCore.signedTotal (fun j v => w j*(cutBit ℚ (cuts j) v-center j)) eps v)^2) /
        (Fintype.card V:ℚ)≤H^2)
    (d : J→ℕ)
    (hd : ∀j,(d j:ℚ)≤rate 36*(3*p^2*(E.card:ℚ)*w j/(64*H)))
    (hbudget : (∑j, (4*(E.card:ℚ)*1296)/
      (rate 36*(3*p^2*(E.card:ℚ)*w j/(64*H)))^2)<1) :
    ∃ mark orientation : E→Bool,∀j,
      d j≤SeparatedRank.endpointImbalance (MatchingThinning.matching E hloop mark orientation).endpoint
        (cuts j) := by
  let f := fun j (e:E) => cutDifference ℚ (cuts j) e.1
  let μ : E→ℚ := fun _ => 1/(E.card:ℚ)
  let k : ℚ := p/(2*H)
  let weight := fun j => k*w j
  let margin := fun j => rate 36*(3*p^2*(E.card:ℚ)*w j/(64*H))
  have hcard : 2*(E.card:ℚ) = 3*(Fintype.card V:ℚ) := by exact_mod_cast regular_edge_count E 3 hreg
  have hV : 0<(Fintype.card V:ℚ) := by exact_mod_cast (Fintype.card_pos (α:=V))
  have hE : 0<(E.card:ℚ) := by linarith only [hcard,hV]
  have hμ : ∀e,0≤μ e := fun _ => by dsimp [μ]; positivity
  have hk : 0<k := by dsimp [k]; positivity
  have hn (t : E→ℚ) : (∑e,μ e*t e)=(∑e,t e)/E.card := by
    simp only [μ,←Finset.mul_sum]
    ring
  have hweight : ∀j,weight j≤1 := by
    intro j
    calc
      _ ≤ k*H := mul_le_mul_of_nonneg_left (hwH j) hk.le
      _ = p/2 := by unfold k; field_simp [hH.ne']
      _ ≤ _ := by linarith only [hp1]
  have he (j : J) : p≤∑e,μ e*(f j e)^2 := by
    rw [hn]
    change p≤(∑e:E,(cutDifference ℚ (cuts j) e.1)^2)/E.card
    rw [Finset.sum_coe_sort E (fun e=> (cutDifference ℚ (cuts j) e)^2),cut_energy_eq_boundary]
    exact hbnd j
  have hm (eps : J→Bool) : (∑ e,μ e*(BangCore.signedTotal (fun j e => weight j*f j e) eps e)^2)≤p := by
    let cell := fun j v => w j*(cutBit ℚ (cuts j) v-center j)
    have hDiff (j : J) (e : V×V) :
        cell j e.1-cell j e.2=w j*cutDifference ℚ (cuts j) e := by
      dsimp [cell,cutDifference]
      ring
    have hm₀ := cubic_signed_edge_moment E hreg (fun j => BangCore.bitSign (eps j)) cell H (hmoment eps)
    simp only [hDiff] at hm₀
    have hsum (e : E) : BangCore.signedTotal (fun j e => weight j*f j e) eps e =
        k*(∑ j,BangCore.bitSign (eps j)*(w j*cutDifference ℚ (cuts j) e.1)) := by
      rw [BangCore.signedTotal,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [f,weight]
      ring
    rw [hn]
    simp_rw [hsum,mul_pow,←Finset.mul_sum]
    rw [mul_div_assoc,Finset.sum_coe_sort E (fun e=>
      (∑j,BangCore.bitSign (eps j)*(w j*cutDifference ℚ (cuts j) e))^2)]
    calc
      _ ≤ k^2*(2*H)^2 := mul_le_mul_of_nonneg_left hm₀ (sq_nonneg k)
      _ = p^2 := by unfold k; field_simp [hH.ne']
      _ ≤ p := by nlinarith only [mul_le_mul_of_nonneg_left hp1 hp.le]
  obtain ⟨b,hb,hc⟩ := WeightedHybrid.weighted_correlation μ f weight p hμ
    (fun j => mul_pos hk (hw j)) hweight (fun j e=>abs_cutDifference_le_one (cuts j) e.1) he hm
  have hCorr (j : J) : 3*p^2*(E.card:ℚ)*w j/(32*H)≤|∑e : E,b e*f j e| := by
    have h := hc j
    simp_rw [mul_assoc] at h
    rw [hn,abs_div,abs_of_pos hE,le_div_iff₀ hE] at h
    convert h using 1
    unfold weight k
    ring
  apply select_weighted_matching E hloop 36
    (ThinningBlockBounds.block_card_le E 3 (fun v => (hreg v).le))
    cuts b hb margin d (fun j => by dsimp [margin]; have r := rate_pos 36; have hwj := hw j; positivity) hd
  · intro j
    calc
      _ = rate 36*(3*p^2*(E.card:ℚ)*w j/(32*H)) := by unfold margin; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hCorr j) (rate_pos 36).le
  · exact hbudget

#print axioms select_weighted_matching
#print axioms weighted_cubic_cut_matching
end Paper5.HybridClosure