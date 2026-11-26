import P5HybridClosurePorts
import HybridFrontier

/-! Actual mixed fixed-affine source term counts on one common oriented
induced matching. The final output alone is integral: the field-valued
source-group terms and their coefficients can be signed or fractional. -/
namespace Paper5.HybridClosure
open scoped BigOperators Classical

variable {V I IM ID AM AD TM TD R S K : Type*}
  [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  [Fintype AM] [DecidableEq AM] [Fintype AD] [DecidableEq AD]
  [Fintype TM] [Fintype TD] [CommRing R] [CommRing S] [Nontrivial S] [Field K]

open GroupProducts SeparatedRank

theorem matching_group_term_rank {Q G : Type*} [Fintype G] [DecidableEq G]
    {L : V→Q→G} (t : GroupTerm L K) (symbols : Q→Finset G)
    (e : (I×Bool)↪V) (d : ℕ)
    (hGap : d≤endpointImbalance e (EmpiricalCutMoments.labelCut L id symbols t.coordinate)) :
    (((t.toVertexTerm symbols).onTransversal e).matrix).rank≤2^(Fintype.card I-d) := by
  let z := (t.toVertexTerm symbols).onTransversal e
  have h : d≤z.imbalance := hGap
  exact z.rank_le.trans (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_left h _))

theorem cloned_fixed_mixed_affine_residue (F : Finset (V×V)) (left right : F→Fin 4)
    (matching : PinnedCNF.InducedMatching F I)
    (L_M : V→IM→AM) (L_D : V→ID→AD)
    (symbols_M : IM→Finset AM) (symbols_D : ID→Finset AD)
    (terms_M : TM→GroupTerm L_M K) (terms_D : TD→GroupTerm L_D K)
    (dM dD : ℕ) (dMle : dM≤Fintype.card I) (dDle : dD≤Fintype.card I)
    (hM : ∀ i, dM≤endpointImbalance matching.endpoint
      (EmpiricalCutMoments.labelCut L_M id symbols_M i))
    (hD : ∀ j, dD≤endpointImbalance matching.endpoint
      (EmpiricalCutMoments.labelCut L_D id symbols_D j))
    (embed : R→+*K) (residue : R→+*S) (hinj : Function.Injective embed)
    (output : (V→Bool)→R)
    (repr : ∀σ,embed (output σ)=(∑t,(terms_M t).value σ)+∑t,(terms_D t).value σ)
    (correct : ∀σ,residue (output σ)=(PinnedCNF.modelCount (MainClonedCNF.formula F left right σ):S)) :
    (1:ℚ)≤(Fintype.card TM:ℚ)/(2:ℚ)^dM+(Fintype.card TD:ℚ)/(2:ℚ)^dD := by
  let B : Matrix (I→Bool) (I→Bool) R := fun x y => output (matching.restrictSigns x y)
  have hres : residue.mapMatrix B=matching.countMatrix S := by
    ext x y
    have h := correct (matching.restrictSigns x y)
    rw [MainClonedCNF.modelCount_cloned] at h
    exact h
  have hr := IntegralOutputTransfer.full_rank_of_residue embed residue hinj B
    (matching.countMatrix S) hres (matching.countMatrix_det_isUnit S).ne_zero
  let B_M := fun t => (((terms_M t).toVertexTerm symbols_M).onTransversal matching.endpoint).matrix
  let B_D := fun t => (((terms_D t).toVertexTerm symbols_D).onTransversal matching.endpoint).matrix
  have hsum : embed.mapMatrix B=(∑t,B_M t)+∑t,B_D t := by
    ext x y
    have h := repr (matching.restrictSigns x y)
    change embed (output (matching.restrictSigns x y))=(∑t,B_M t) x y+(∑t,B_D t) x y
    rw [Matrix.sum_apply,Matrix.sum_apply]
    simpa only [B_M,B_D,VertexTerm.onTransversal_apply,GroupTerm.toVertexTerm_value] using h
  have hm (t : TM) : (B_M t).rank≤(1:ℕ)*2^(Fintype.card I-dM) := by
    rw [one_mul]
    exact matching_group_term_rank _ _ matching.endpoint dM (hM (terms_M t).coordinate)
  have hd (t : TD) : (B_D t).rank≤(1:ℕ)*2^(Fintype.card I-dD) := by
    rw [one_mul]
    exact matching_group_term_rank _ _ matching.endpoint dD (hD (terms_D t).coordinate)
  have hrank : (embed.mapMatrix B).rank=2^Fintype.card I := by
    simpa only [Fintype.card_fun,Fintype.card_bool] using hr
  apply HybridFrontier.normalized_two_route (Fintype.card I) dM dD _ _ dMle dDle
  simpa using HybridFrontier.two_route_budget (Fintype.card I) dM dD (embed.mapMatrix B)
    B_M B_D (fun _ => 1) (fun _ => 1) hrank hsum hm hd

theorem minimum_depth_term_count {nM nD dM dD d : ℕ}
    (hM : d≤dM) (hD : d≤dD)
    (h : (1:ℚ)≤(nM:ℚ)/(2:ℚ)^dM+(nD:ℚ)/(2:ℚ)^dD) : 2^d ≤ nM+nD := by
  have hm : (2:ℚ)^d≤(2:ℚ)^dM := pow_le_pow_right₀ (by norm_num) hM
  have hd : (2:ℚ)^d≤(2:ℚ)^dD := pow_le_pow_right₀ (by norm_num) hD
  have hq : (1:ℚ)≤((nM:ℚ)+(nD:ℚ))/(2:ℚ)^d := by
    rw [add_div]
    exact h.trans (add_le_add (div_le_div_of_nonneg_left (by positivity) (by positivity) hm)
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hd))
  have hh := (le_div_iff₀ (show 0<(2:ℚ)^d by positivity)).mp hq
  rw [one_mul] at hh
  exact_mod_cast hh

#print axioms matching_group_term_rank
#print axioms cloned_fixed_mixed_affine_residue
#print axioms minimum_depth_term_count
end Paper5.HybridClosure