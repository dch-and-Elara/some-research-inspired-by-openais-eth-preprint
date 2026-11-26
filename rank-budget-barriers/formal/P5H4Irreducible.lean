import RBLocalProfile
import Mathlib.RingTheory.Multiplicity

/-! H4 at a general monic irreducible polynomial, not just a rational
point. The image is multiplication in the literal quotient by a power. -/
namespace P5H4
open Polynomial Matrix Module
open scoped Classical BigOperators

variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]

/-- Matrix image length over the scalar field in an actual polynomial
quotient. This definition also permits rectangular matrices. -/
noncomputable def quotientMul (A : Matrix m n K[X]) (f : K[X]) :
    (n → AdjoinRoot f) →ₗ[K] (m → AdjoinRoot f) :=
  ((A.map (AdjoinRoot.mk f)).mulVecLin).restrictScalars K

noncomputable def quotientLength (A : Matrix m n K[X]) (f : K[X]) : ℕ :=
  Module.finrank K (LinearMap.range (quotientMul A f))

theorem polynomial_finiteMultiplicity {f p : K[X]} (hf : 0 < f.natDegree) (hp : p ≠ 0) :
    FiniteMultiplicity f p := by
  refine ⟨p.natDegree, fun h => ?_⟩
  have hd := natDegree_le_of_dvd h hp
  rw [natDegree_pow, Nat.mul_comm] at hd
  have hl := Nat.mul_le_mul_right (p.natDegree+1) (show 1 ≤ f.natDegree by omega)
  simp only [one_mul] at hl
  omega

private theorem lifted_mk (f g : K[X]) (h : g ∣ f) (p : K[X]) :
    AdjoinRoot.algHomOfDvd f g h (AdjoinRoot.mk f p) = AdjoinRoot.mk g p := by
  rw [AdjoinRoot.algHomOfDvd,AdjoinRoot.liftHom_mk,AdjoinRoot.aeval_eq]

theorem quotient_power_dim (f : K[X]) (hm : f.Monic) (k : ℕ) :
    Module.finrank K (AdjoinRoot (f^k)) = f.natDegree*k := by
  rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasisAux' (hm.pow k))]
  simp [natDegree_pow, Nat.mul_comm]

variable [DecidableEq n]

set_option maxHeartbeats 4500000 in
/-- Weighted exact clipped profile for a nonzero diagonal at any monic
irreducible f. The multiplier natDegree f is essential. -/
theorem irreducible_diagonal_length (f : K[X]) (hm : f.Monic) (hf : Irreducible f)
    (a : n → K[X]) (ha : ∀ i, a i ≠ 0) (k : ℕ) :
    quotientLength (diagonal a) (f^k) =
      ∑ i, (f.natDegree * (k-min k (multiplicity f (a i)))) := by
  have hp : Prime f := hf.prime
  have hd : 0 < f.natDegree := by
    by_contra! h
    exact hf.not_isUnit (by
      rw [hm.natDegree_eq_zero.mp (Nat.eq_zero_of_le_zero h)]
      exact isUnit_one)
  let e (i : n) := min k (multiplicity f (a i))
  have hek (i : n) : e i ≤ k := min_le_left ..
  let Q : (n → AdjoinRoot (f^k)) →ₗ[K] ((i : n) → AdjoinRoot (f^(e i))) :=
    LinearMap.pi fun i => (AdjoinRoot.algHomOfDvd _ _ (pow_dvd_pow f (hek i))).toLinearMap.comp
      (LinearMap.proj i)
  letI : Module.Finite K (AdjoinRoot (f^k)) := (hm.pow k).finite_adjoinRoot
  letI (i : n) : Module.Finite K (AdjoinRoot (f^e i)) := (hm.pow (e i)).finite_adjoinRoot
  have hsurj : Function.Surjective Q := by
    intro y
    choose p hy using fun i => AdjoinRoot.mk_surjective (y i)
    refine ⟨fun i => AdjoinRoot.mk (f^k) (p i), ?_⟩
    funext i
    exact (lifted_mk _ _ (pow_dvd_pow f (hek i)) (p i)).trans (hy i)
  have hker : LinearMap.range (quotientMul (diagonal a) (f^k)) ≤ LinearMap.ker Q := by
    rintro _ ⟨x,rfl⟩
    apply LinearMap.mem_ker.mpr
    funext i
    change AdjoinRoot.algHomOfDvd _ _ (pow_dvd_pow f (hek i))
      (((diagonal a).map (AdjoinRoot.mk (f^k)) *ᵥ x) i) = 0
    rw [Matrix.diagonal_map (map_zero (AdjoinRoot.mk (f^k))), Matrix.mulVec_diagonal,map_mul]
    have hdiv : f^e i ∣ a i := pow_dvd_of_le_multiplicity (min_le_right ..)
    change (AdjoinRoot.algHomOfDvd _ _ _ (AdjoinRoot.mk _ (a i))) * _ = 0
    rw [lifted_mk,AdjoinRoot.mk_eq_zero.mpr hdiv,zero_mul]
  have hQ := Q.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj,finrank_top,Module.finrank_pi_fintype,
    Module.finrank_pi_fintype] at hQ
  simp only [quotient_power_dim f hm,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hQ
  have heq : (∑ i, f.natDegree*(k-e i))+(∑ i,f.natDegree*e i) =
      Fintype.card n * (f.natDegree*k) := by
    rw [← Finset.sum_add_distrib]
    have h (i : n) : f.natDegree*(k-e i)+f.natDegree*e i = f.natDegree*k := by
      rw [← Nat.mul_add, Nat.sub_add_cancel (hek i)]
    simp [h]
  change (∑ i, f.natDegree*e i) + finrank K (LinearMap.ker Q) = Fintype.card n * (f.natDegree*k) at hQ
  have hle := Submodule.finrank_mono hker
  change quotientLength (diagonal a) (f^k) ≤ _ at hle
  change quotientLength (diagonal a) (f^k) = ∑ i, f.natDegree*(k-e i)
  refine le_antisymm (by omega) ?_
  let rd : ((i : n) → degreeLT K (f.natDegree*(k-e i))) →ₗ[K] (n → AdjoinRoot (f^k)) :=
    LinearMap.pi fun i => (AdjoinRoot.mkₐ (f^k)).toLinearMap.comp
      ((degreeLT K (f.natDegree*(k-e i))).subtype.comp (LinearMap.proj i))
  let G := (quotientMul (diagonal a) (f^k)).rangeRestrict.comp rd
  have hGi : Function.Injective G := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    funext i
    apply Subtype.ext
    change (v i : K[X]) = 0
    by_contra hn
    have hh := congrArg (fun y => y.val i) hv
    change (((diagonal a).map (AdjoinRoot.mk (f^k))) *ᵥ
      (fun i => AdjoinRoot.mk (f^k) (v i))) i = 0 at hh
    rw [Matrix.diagonal_map (map_zero (AdjoinRoot.mk (f^k))),Matrix.mulVec_diagonal,← map_mul] at hh
    have hdim : (v i : K[X]).natDegree < f.natDegree*(k-e i) :=
      (natDegree_lt_iff_degree_lt hn).mpr (mem_degreeLT.mp (v i).property)
    have hfull : k ≤ multiplicity f (a i * v i) :=
      (polynomial_finiteMultiplicity hd (mul_ne_zero (ha i) hn)).le_multiplicity_of_pow_dvd
        (AdjoinRoot.mk_eq_zero.mp hh)
    rw [multiplicity_mul hp (polynomial_finiteMultiplicity hd (mul_ne_zero (ha i) hn))] at hfull
    have hneeded : k-e i ≤ multiplicity f (v i : K[X]) := by
      dsimp [e]
      omega
    have hdvd : (f^(k-e i)).natDegree ≤ (v i : K[X]).natDegree :=
      natDegree_le_of_dvd (pow_dvd_of_le_multiplicity hneeded) hn
    rw [natDegree_pow, Nat.mul_comm] at hdvd
    exact (not_le_of_gt hdim) hdvd
  have hfin := LinearMap.finrank_le_finrank_of_injective hGi
  letI (i : n) : Module.Finite K (degreeLT K (f.natDegree*(k-e i))) :=
    Module.Finite.equiv (degreeLTEquiv K _).symm
  have hdeg (i : n) : Module.finrank K (degreeLT K (f.natDegree*(k-e i))) =
      f.natDegree*(k-e i) := by
    rw [(degreeLTEquiv K _).finrank_eq,Module.finrank_pi,Fintype.card_fin]
  rw [Module.finrank_pi_fintype] at hfin
  simpa only [hdeg] using hfin

#print axioms polynomial_finiteMultiplicity
#print axioms quotient_power_dim
#print axioms irreducible_diagonal_length
end P5H4
