import RBCoupled
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.Basis

namespace RankBudget
open Polynomial Matrix Module
open scoped BigOperators
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- A full-rank polynomial square matrix has a two-sided diagonalization by
polynomial units. Adapt the PID submodule theorem, without divisibility ordering. -/
theorem polyDiagonalize (P : Matrix n n K[X]) (hp : P.det ≠ 0) :
    ∃ (U V : Matrix n n K[X]) (a : n → K[X]),
      IsUnit U ∧ IsUnit V ∧ U * P * V = Matrix.diagonal a := by
  classical
  let b := Pi.basisFun K[X] n
  have hi : Function.Injective P.mulVecLin := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    by_contra h
    exact hp ((Matrix.exists_mulVec_eq_zero_iff).mp ⟨w, h, hw⟩)
  let e := LinearEquiv.ofInjective P.mulVecLin hi
  obtain ⟨c,a,g,hg⟩ := Submodule.exists_smith_normal_form_of_rank_eq b e.finrank_eq.symm
  let f := g.map e.symm
  have hm : P * b.toMatrix f = b.toMatrix c * diagonal a := by
    ext i j
    rw [Matrix.mul_apply, Matrix.mul_diagonal]
    simp only [Basis.toMatrix_apply, b, Pi.basisFun_repr]
    have h := congrFun (LinearEquiv.ofInjective_symm_apply (h := hi) P.mulVecLin (g j)) i
    change (∑ l, P i l * (f j) l) = (g j : n → K[X]) i at h
    rw [h, hg, Pi.smul_apply, smul_eq_mul, mul_comm]
  have bc (b₁ b₂ : Basis n K[X] (n → K[X])) : b₁.toMatrix b₂ * b₂.toMatrix b₁ = 1 := by
    rw [Basis.toMatrix_mul_toMatrix, Basis.toMatrix_self]
  have bu (b₁ b₂ : Basis n K[X] (n → K[X])) : IsUnit (b₁.toMatrix b₂) :=
    ⟨⟨_, b₂.toMatrix b₁, bc _ _, bc _ _⟩, rfl⟩
  refine ⟨c.toMatrix b, b.toMatrix f, a, bu _ _, bu _ _, ?_⟩
  rw [Matrix.mul_assoc, hm, ← Matrix.mul_assoc, bc, Matrix.one_mul]

/-- The total degree of diagonalized nonzero entries is intrinsic. -/
theorem diagonalDegree (P U V : Matrix n n K[X]) (a : n → K[X])
    (hp : P.det ≠ 0) (hu : IsUnit U) (hv : IsUnit V) (hm : U * P * V = diagonal a) :
    (∀ i, a i ≠ 0) ∧ (∑ i, (a i).natDegree) = P.det.natDegree := by
  have h := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at h
  have hdu := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have hdv := (Matrix.isUnit_iff_isUnit_det _).mp hv
  have ha : ∀ i, a i ≠ 0 := by
    have hpn : (∏ i, a i) ≠ 0 := h ▸ mul_ne_zero (mul_ne_zero hdu.ne_zero hp) hdv.ne_zero
    exact fun i => Finset.prod_ne_zero_iff.mp hpn i (Finset.mem_univ i)
  refine ⟨ha, ?_⟩
  have hd := congrArg Polynomial.natDegree h
  rwa [Polynomial.natDegree_prod _ _ fun i _ => ha i,
    Polynomial.natDegree_mul (mul_ne_zero hdu.ne_zero hp) hdv.ne_zero,
    Polynomial.natDegree_mul hdu.ne_zero hp,
    Polynomial.natDegree_eq_zero_of_isUnit hdu, Polynomial.natDegree_eq_zero_of_isUnit hdv,
    zero_add, add_zero, eq_comm] at hd

/-- **Sharp determinant budget for actual jet image lengths.** Unlike the
entry-degree corollary, no entry-degree bound is assumed. Change polynomial
bases globally, then inject coordinatewise bounded polynomial inputs. -/
theorem jetDefectLeDetDegree (P : Matrix n n K[X]) (s : Finset K) (k : K → ℕ)
    (hp : P.det ≠ 0) :
    (∑ t ∈ s, (Fintype.card n * k t - jetLength P t (k t))) ≤ P.det.natDegree := by
  classical
  obtain ⟨U,V,a,hu,hv,hdiag⟩ := polyDiagonalize P hp
  obtain ⟨ha,hd⟩ := diagonalDegree P U V a hp hu hv hdiag
  let M := ∑ t ∈ s, k t
  let m (i : n) := M - (a i).natDegree
  letI (t : ↥s) : Module.Finite K (Jet t.1 (k t)) := ((monic_X_sub_C t.1).pow (k t)).finite_adjoinRoot
  let rd (t : ↥s) : ((i : n) → degreeLT K (m i)) →ₗ[K] (n → Jet t.1 (k t)) :=
    LinearMap.pi fun i => (AdjoinRoot.mkₐ ((X - C t.1) ^ k t)).toLinearMap.comp
      ((degreeLT K (m i)).subtype.comp (LinearMap.proj i))
  let G : ((i : n) → degreeLT K (m i)) →ₗ[K] ((t : ↥s) → LinearMap.range (jetMul P t.1 (k t))) :=
    LinearMap.pi fun t => (jetMul P t.1 (k t)).rangeRestrict.comp ((jetMul V t.1 (k t)).comp (rd t))
  have hin : Function.Injective G := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hzero
    let w : n → K[X] := fun j => v j
    funext i
    apply Subtype.ext
    change w i = 0
    by_contra hi
    have hz : ∀ t ∈ s, (X - C t) ^ k t ∣ (a i * w i) := by
      intro t ht
      let q : K[X] := (X - C t) ^ k t
      let φ := AdjoinRoot.mk q
      apply AdjoinRoot.mk_eq_zero.mp
      have hraw : P.map φ *ᵥ (V.map φ *ᵥ (φ ∘ w)) = 0 :=
        congrArg Subtype.val (congrFun hzero ⟨t,ht⟩)
      have hrepl : φ ∘ (V *ᵥ w) = (V.map φ *ᵥ φ ∘ w) := funext fun j => φ.map_mulVec V w j
      have hp0 : φ ∘ (P *ᵥ (V *ᵥ w)) = 0 := by
        funext j
        change φ ((P *ᵥ V *ᵥ w) j) = 0
        rw [RingHom.map_mulVec, hrepl, hraw]; rfl
      have zu : φ ((U *ᵥ P *ᵥ V *ᵥ w) i) = 0 := by
        rw [RingHom.map_mulVec, hp0, Matrix.mulVec_zero]; rfl
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hdiag, Matrix.mulVec_diagonal] at zu
      exact zu
    have lo := multiplicityBudget _ (mul_ne_zero (ha i) hi) s k hz
    rw [Polynomial.natDegree_mul (ha i) hi] at lo
    have hwi : (w i).natDegree < m i := (natDegree_lt_iff_degree_lt hi).mpr (mem_degreeLT.mp (v i).property)
    dsimp [m, M] at hwi
    omega
  have hi := LinearMap.finrank_le_finrank_of_injective hin
  letI (i : n) : Module.Finite K (degreeLT K (m i)) := Module.Finite.equiv (degreeLTEquiv K (m i)).symm
  have hfi (i : n) : Module.finrank K (degreeLT K (m i)) = m i := by
    rw [(degreeLTEquiv K (m i)).finrank_eq, Module.finrank_pi, Fintype.card_fin]
  rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype] at hi
  have hcap : ∑ i, m i ≤ ∑ t ∈ s, jetLength P t (k t) := by
    rw [← Finset.sum_coe_sort s (fun t => jetLength P t (k t))]
    simpa only [hfi] using hi
  have hex : Fintype.card n * M ≤ (∑ i, m i) + P.det.natDegree := by
    rw [← hd, ← Finset.sum_add_distrib]
    calc
      Fintype.card n * M = ∑ _i : n, M := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => by dsimp [m]; omega
  have hout : (∑ t ∈ s, (Fintype.card n * k t - jetLength P t (k t))) +
      (∑ t ∈ s, jetLength P t (k t)) = Fintype.card n * M := by
    dsimp [M]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun t _ => Nat.sub_add_cancel (jetLength_le P t (k t))
  omega

/-- Simultaneous sharp determinant and final-output bounds on the same
actual jet lengths, allowing a second family E on the same observation. -/
theorem sharpCoupledBudget (P : Matrix n n K[X]) (s : Finset K) (k : K → ℕ)
    (ℓ : ∀ t, Jet t (k t) →ₗ[K] K) (hp : P.det ≠ 0) (M E : Matrix n n K)
    (h : M = (∑ t ∈ s, P.map (fun p => ℓ t (AdjoinRoot.mk ((X - C t) ^ k t) p))) + E) :
    (∑ t ∈ s, (Fintype.card n * k t - jetLength P t (k t))) ≤ P.det.natDegree ∧
    M.rank ≤ (∑ t ∈ s, jetLength P t (k t)) + E.rank := by
  refine ⟨jetDefectLeDetDegree P s k hp, ?_⟩
  rw [h]
  refine (commonRank_add _ _).trans (Nat.add_le_add_right ?_ _)
  exact (commonRank_sum ..).trans (Finset.sum_le_sum fun t _ => readJet_rank_le P t (k t) (ℓ t))

end RankBudget