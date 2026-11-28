import P5HybridClosureMatching
import P5HybridClosureAffine

/-! Separate centered energy estimates for the MAIN and D label laws
combine on the *same* physical vertices.  This uses finite
Cauchy Schwarz, not inter-layout independence. -/
namespace Paper5.HybridClosure
open scoped BigOperators Classical
open GraphCutMoments EmpiricalCutMoments

theorem mean_square_add_bound {V : Type*} [Fintype V] [Nonempty V] (f g : V→ℚ)
    (A B : ℚ) (hA : 0≤A) (hB : 0≤B)
    (hf : (∑v,(f v)^2)/(Fintype.card V:ℚ)≤A^2)
    (hg : (∑v,(g v)^2)/(Fintype.card V:ℚ)≤B^2) :
    (∑v,(f v+g v)^2)/(Fintype.card V:ℚ)≤(A+B)^2 := by
  let N : ℚ := Fintype.card V
  have hN : 0<N := by dsimp [N]; exact_mod_cast (Fintype.card_pos (α:=V))
  have hX : (∑v,(f v)^2)≤A^2*N := (div_le_iff₀ hN).mp hf
  have hY : (∑v,(g v)^2)≤B^2*N := (div_le_iff₀ hN).mp hg
  have hxy := (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g).trans
    (mul_le_mul hX hY (Finset.sum_nonneg (fun v _ => sq_nonneg (g v))) (by positivity))
  have hxy₂ : (∑v,f v*g v)^2≤(A*B*N)^2 := by simpa only [show (A^2*N)*(B^2*N)=(A*B*N)^2 by ring] using hxy
  have hxy₃ : (∑v,f v*g v)≤A*B*N := by
    by_contra! h
    have hpos := mul_pos (sub_pos.mpr h)
      (show 0<(∑v,f v*g v)+A*B*N by linarith only [h, mul_nonneg (mul_nonneg hA hB) hN.le])
    nlinarith only [hpos,hxy₂]
  apply (div_le_iff₀ hN).mpr
  have hEq : (∑v,(f v+g v)^2)=(∑v,(f v)^2)+(∑v,(g v)^2)+2*∑v,f v*g v := by
    calc
      _ = ∑v,((f v)^2+((g v)^2+2*(f v*g v))) := by exact Finset.sum_congr rfl (fun _ _ => by ring)
      _ = _ := by rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.mul_sum,add_assoc]
  rw [hEq]
  calc
    _ ≤ A^2*N+B^2*N+2*(A*B*N) :=
      add_le_add (add_le_add hX hY) (mul_le_mul_of_nonneg_left hxy₃ (by decide))
    _ = _ := by ring

section Route
variable {V I A : Type*}
  [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype I] [DecidableEq I] [Fintype A] [DecidableEq A] [Nonempty A]

theorem weighted_one_route_moment (L : V→I→A) (sym : I→Finset A) (C w R : ℚ)
    (hC : 0≤C)
    (hdom : ∀x,empiricalLaw L x≤C*ProductVariance.uniformWeight (I→A))
    (hR : w^2*C*(Fintype.card I:ℚ)≤R^2) (eps : I→Bool) :
    (∑v,(BangCore.signedTotal (fun i v=>w*(cutBit ℚ (labelCut L id sym i) v-
      cutDensity (labelCut L id sym i))) eps v)^2)/(Fintype.card V:ℚ)≤R^2 := by
  let f := fun i v => cutBit ℚ (labelCut L id sym i) v-cutDensity (labelCut L id sym i)
  have hbase := vertex_signed_moment L id sym C hC hdom eps
  have hcoord (i : I) : ProductVariance.coordinateCount (id : I→I) i=1 := by
    unfold ProductVariance.coordinateCount
    have hh : (Finset.univ.filter fun j : I => id j=i)={i} := by ext x; simp
    rw [hh,Finset.card_singleton]
  simp only [hcoord,Nat.cast_one,one_pow,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hbase
  have hfactor (v : V) : BangCore.signedTotal (fun i v=>w*f i v) eps v =
      w*BangCore.signedTotal f eps v := by
    simp only [BangCore.signedTotal,Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _=>by ring)
  change (∑v,(BangCore.signedTotal (fun i v=>w*f i v) eps v)^2)/_≤_
  simp_rw [hfactor,mul_pow,←Finset.mul_sum,mul_div_assoc]
  calc
    _ ≤ w^2*(C*Fintype.card I) := mul_le_mul_of_nonneg_left hbase (sq_nonneg _)
    _ ≤ _ := by simpa only [mul_assoc] using hR
end Route

section TwoRoutes
variable {V IM ID AM AD : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  [Fintype IM] [DecidableEq IM] [Fintype ID] [DecidableEq ID]
  [Fintype AM] [DecidableEq AM] [Nonempty AM]
  [Fintype AD] [DecidableEq AD] [Nonempty AD]

def pairedCuts (L_M : V→IM→AM) (L_D : V→ID→AD) (s_M : IM→Finset AM) (s_D : ID→Finset AD) :
    IM⊕ID→Finset V := Sum.elim (labelCut L_M id s_M) (labelCut L_D id s_D)

def pairedWeights (wM wD : ℚ) : IM⊕ID→ℚ := Sum.elim (fun _=>wM) (fun _=>wD)

theorem weighted_two_route_moment (L_M : V→IM→AM) (L_D : V→ID→AD)
    (s_M : IM→Finset AM) (s_D : ID→Finset AD)
    (C_M C_D wM wD H_M H_D : ℚ)
    (hCM : 0≤C_M) (hCD : 0≤C_D) (hHM : 0≤H_M) (hHD : 0≤H_D)
    (hdomM : ∀x,empiricalLaw L_M x≤C_M*ProductVariance.uniformWeight (IM→AM))
    (hdomD : ∀x,empiricalLaw L_D x≤C_D*ProductVariance.uniformWeight (ID→AD))
    (hM : wM^2*C_M*(Fintype.card IM:ℚ)≤H_M^2)
    (hD : wD^2*C_D*(Fintype.card ID:ℚ)≤H_D^2) (eps : IM⊕ID→Bool) :
    let cuts := pairedCuts L_M L_D s_M s_D
    let w : IM⊕ID→ℚ := pairedWeights wM wD
    (∑v,(BangCore.signedTotal (fun j v=>w j*(cutBit ℚ (cuts j) v-cutDensity (cuts j))) eps v)^2)/
      (Fintype.card V:ℚ)≤(H_M+H_D)^2 := by
  let cuts := pairedCuts L_M L_D s_M s_D
  let w : IM⊕ID→ℚ := pairedWeights wM wD
  let fM := BangCore.signedTotal (fun j v=>wM*(cutBit ℚ (labelCut L_M id s_M j) v-
    cutDensity (labelCut L_M id s_M j))) (eps ∘ Sum.inl)
  let fD := BangCore.signedTotal (fun j v=>wD*(cutBit ℚ (labelCut L_D id s_D j) v-
    cutDensity (labelCut L_D id s_D j))) (eps ∘ Sum.inr)
  have hp (v : V) : BangCore.signedTotal
      (fun j v=>w j*(cutBit ℚ (cuts j) v-cutDensity (cuts j))) eps v=fM v+fD v := by
    rw [BangCore.signedTotal,Fintype.sum_sum_type]
    rfl
  change (∑v,(BangCore.signedTotal
    (fun j v=>w j*(cutBit ℚ (cuts j) v-cutDensity (cuts j))) eps v)^2)/_≤_
  simp only [hp]
  exact mean_square_add_bound fM fD H_M H_D hHM hHD
    (weighted_one_route_moment L_M s_M C_M wM H_M hCM hdomM hM _)
    (weighted_one_route_moment L_D s_D C_D wD H_D hCD hdomD hD _)
end TwoRoutes

#print axioms mean_square_add_bound
#print axioms weighted_one_route_moment
#print axioms weighted_two_route_moment
end Paper5.HybridClosure