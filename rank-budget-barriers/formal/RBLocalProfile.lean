import RBSharp
import RBFactor
namespace RankBudget
open Matrix Polynomial Module
open scoped BigOperators

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
private theorem jetMul_comp' (A B : Matrix n n K[X]) (t : K) (k : ℕ) :
    jetMul (A*B) t k = (jetMul A t k).comp (jetMul B t k) := by
  apply LinearMap.ext
  intro x
  change (A * B).map (AdjoinRoot.mk ((X - C t) ^ k)) *ᵥ x =
    (A.map _) *ᵥ (B.map _) *ᵥ x
  rw [Matrix.map_mul, Matrix.mulVec_mulVec]

omit [DecidableEq n] in
private theorem jetLength_mul_le (A B : Matrix n n K[X]) (t : K) (k : ℕ) :
    jetLength (A*B) t k ≤ jetLength A t k ∧ jetLength (A*B) t k ≤ jetLength B t k := by
  letI : Module.Finite K (Jet t k) := ((monic_X_sub_C t).pow k).finite_adjoinRoot
  unfold jetLength
  rw [jetMul_comp']
  refine ⟨Submodule.finrank_mono (LinearMap.range_comp_le_range _ _), ?_⟩
  rw [LinearMap.range_comp]
  exact Submodule.finrank_map_le _ _

omit [DecidableEq n] in
private theorem len_sandwich (U P V : Matrix n n K[X]) (t : K) (k : ℕ) :
    jetLength (U * P * V) t k ≤ jetLength P t k := by
  have h1 : jetLength (U * P * V) t k ≤ jetLength (U * P) t k :=
    (jetLength_mul_le (U * P) V t k).1
  have h2 : jetLength (U * P) t k ≤ jetLength P t k := (jetLength_mul_le U P t k).2
  exact h1.trans h2

theorem jetLength_unimodular (P U V : Matrix n n K[X]) (hu : IsUnit U) (hv : IsUnit V)
    (t : K) (k : ℕ) : jetLength (U * P * V) t k = jetLength P t k := by
  obtain ⟨u,hue⟩ := hu
  obtain ⟨v,hve⟩ := hv
  let U' : Matrix n n K[X] := u.inv
  let V' : Matrix n n K[X] := v.inv
  have hl : U' * U = 1 := hue ▸ u.inv_val
  have hr : V * V' = 1 := hve ▸ v.val_inv
  have hundo : U' * (U * P * V) * V' = P := by
    calc
      _ = ((U' * U) * P) * (V * V') := by simp only [Matrix.mul_assoc]
      _ = P := by rw [hl,hr,Matrix.one_mul,Matrix.mul_one]
  refine le_antisymm (len_sandwich U P V t k) ?_
  have h := len_sandwich U' (U * P * V) V' t k
  rwa [hundo] at h

private theorem jetFinrank' (t : K) (k : ℕ) : Module.finrank K (Jet t k) = k := by
  rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasisAux' ((monic_X_sub_C t).pow k))]
  simp

private theorem mapJet_mk (f g : K[X]) (h : g ∣ f) (p : K[X]) :
    AdjoinRoot.algHomOfDvd f g h (AdjoinRoot.mk f p) = AdjoinRoot.mk g p := by
  rw [AdjoinRoot.algHomOfDvd, AdjoinRoot.liftHom_mk, AdjoinRoot.aeval_eq]

/-- Exact local-multiplication image dimension for a diagonal polynomial
matrix. Each factor is charged min(k,ord_t), not k times its residue defect. -/
theorem jetLength_diagonal (a : n → K[X]) (ha : ∀ i, a i ≠ 0) (t : K) (k : ℕ) :
    jetLength (diagonal a) t k = ∑ i, (k - min k (rootMultiplicity t (a i))) := by
  classical
  let q (l : ℕ) : K[X] := (X - C t)^l
  let e (i : n) := min k (rootMultiplicity t (a i))
  have he (i : n) : e i ≤ k := Nat.min_le_left .. 
  let lift (i : n) := AdjoinRoot.algHomOfDvd (q k) (q (e i)) (pow_dvd_pow _ (he i))
  let Q : (n → Jet t k) →ₗ[K] ((i : n) → Jet t (e i)) :=
    LinearMap.pi fun i => (lift i).toLinearMap.comp (LinearMap.proj i)
  letI : Module.Finite K (Jet t k) := ((monic_X_sub_C t).pow k).finite_adjoinRoot
  letI (i : n) : Module.Finite K (Jet t (e i)) := ((monic_X_sub_C t).pow (e i)).finite_adjoinRoot
  have hsurj : Function.Surjective Q := by
    intro y
    choose w hw using fun i => AdjoinRoot.mk_surjective (y i)
    refine ⟨fun i => AdjoinRoot.mk (q k) (w i), ?_⟩
    funext i
    exact (mapJet_mk (q k) (q (e i)) (pow_dvd_pow _ (he i)) (w i)).trans (hw i)
  have hker : LinearMap.range (jetMul (diagonal a) t k) ≤ LinearMap.ker Q := by
    rintro _ ⟨x, rfl⟩
    apply LinearMap.mem_ker.mpr
    funext i
    change lift i (((diagonal a).map (AdjoinRoot.mk (q k)) *ᵥ x) i) = 0
    rw [Matrix.diagonal_map (map_zero (AdjoinRoot.mk (q k))), Matrix.mulVec_diagonal, map_mul]
    have hdiv : q (e i) ∣ a i := (Polynomial.le_rootMultiplicity_iff (ha i)).mp (Nat.min_le_right ..)
    change (AdjoinRoot.algHomOfDvd _ _ _ (AdjoinRoot.mk _ (a i))) * _ = 0
    rw [mapJet_mk, AdjoinRoot.mk_eq_zero.mpr hdiv, zero_mul]
  have hd := Q.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_pi_fintype,
    Module.finrank_pi_fintype] at hd
  simp only [jetFinrank', Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hd
  have hes : (∑ i, (k-e i)) + (∑ i, e i) = Fintype.card n * k := by
    rw [← Finset.sum_add_distrib]
    simp [Nat.sub_add_cancel (he _)]
  change (∑ i, e i) + Module.finrank K (LinearMap.ker Q) = Fintype.card n * k at hd
  have hle := Submodule.finrank_mono hker
  change jetLength (diagonal a) t k ≤ _ at hle
  change jetLength (diagonal a) t k = ∑ i, (k-e i)
  refine le_antisymm (by omega) ?_
  let rd : ((i : n) → degreeLT K (k-e i)) →ₗ[K] (n → Jet t k) :=
    LinearMap.pi fun i => (AdjoinRoot.mkₐ (q k)).toLinearMap.comp
      ((degreeLT K (k-e i)).subtype.comp (LinearMap.proj i))
  let G := (jetMul (diagonal a) t k).rangeRestrict.comp rd
  have hin : Function.Injective G := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hz
    funext i
    apply Subtype.ext
    change (v i : K[X]) = 0
    by_contra hne
    have hc := congrArg (fun y => y.val i) hz
    change (((diagonal a).map (AdjoinRoot.mk (q k))) *ᵥ (fun i => AdjoinRoot.mk (q k) (v i))) i = 0 at hc
    rw [Matrix.diagonal_map (map_zero (AdjoinRoot.mk (q k))), Matrix.mulVec_diagonal, ← map_mul] at hc
    have lo := (le_rootMultiplicity_iff (mul_ne_zero (ha i) hne)).mpr (AdjoinRoot.mk_eq_zero.mp hc)
    rw [rootMultiplicity_mul (mul_ne_zero (ha i) hne)] at lo
    have hdeg : (v i : K[X]).natDegree < k - e i :=
      (natDegree_lt_iff_degree_lt hne).mpr (mem_degreeLT.mp (v i).property)
    have hroot : rootMultiplicity t (v i : K[X]) ≤ (v i : K[X]).natDegree := by
      have := multiplicityBudget (v i : K[X]) hne {t} (fun x => rootMultiplicity x (v i : K[X]))
        (fun x _ => Polynomial.pow_rootMultiplicity_dvd _ _)
      simpa using this
    dsimp [e] at hdeg
    omega
  have hsize := LinearMap.finrank_le_finrank_of_injective hin
  letI (i : n) : Module.Finite K (degreeLT K (k-e i)) :=
    Module.Finite.equiv (degreeLTEquiv K (k-e i)).symm
  have ds (i : n) : Module.finrank K (degreeLT K (k-e i)) = k-e i := by
    rw [(degreeLTEquiv K _).finrank_eq, Module.finrank_pi, Fintype.card_fin]
  rw [Module.finrank_pi_fintype] at hsize
  simpa only [ds] using hsize

/-- A single polynomial diagonalization determines the full profile at *all*
nodes and all truncation precisions simultaneously. -/
theorem exists_clippedProfile (P : Matrix n n K[X]) (hp : P.det ≠ 0) :
    ∃ a : n → K[X], (∀ i, a i ≠ 0) ∧ (∑ i, (a i).natDegree) = P.det.natDegree ∧
      ∀ (t : K) (k : ℕ), jetLength P t k = ∑ i, (k - min k (rootMultiplicity t (a i))) := by
  obtain ⟨U,V,a,hu,hv,h⟩ := polyDiagonalize P hp
  obtain ⟨ha,hd⟩ := diagonalDegree P U V a hp hu hv h
  refine ⟨a,ha,hd,fun t k => ?_⟩
  rw [← jetLength_unimodular P U V hu hv t k, h, jetLength_diagonal a ha]
omit [DecidableEq n] in
/-- A genuine two-factor jet representation has small multiplication image;
polynomial representatives can be lifted freely, since the error is in q. -/
theorem jetLength_of_factor {r : Type*} [Fintype r] (P E : Matrix n n K[X])
    (A : Matrix n r K[X]) (B : Matrix r n K[X]) (t : K) (k : ℕ)
    (h : P = (X - C t)^k • E + A * B) :
    jetLength P t k ≤ Fintype.card r * k := by
  let q : K[X] := (X - C t)^k
  let φ := AdjoinRoot.mk q
  letI : Module.Finite K (Jet t k) := ((monic_X_sub_C t).pow k).finite_adjoinRoot
  let L := ((A.map φ).mulVecLin).restrictScalars K
  let H := ((B.map φ).mulVecLin).restrictScalars K
  have hq : φ q = 0 := AdjoinRoot.mk_eq_zero.mpr (dvd_refl _)
  have hP : P.map φ = A.map φ * B.map φ := by
    rw [← Matrix.map_mul, h]
    ext i j
    change φ (q * E i j + (A * B) i j) = φ ((A * B) i j)
    rw [map_add, map_mul, hq, zero_mul, zero_add]
  have heq : jetMul P t k = L.comp H := by
    apply LinearMap.ext
    intro v
    change P.map φ *ᵥ v = A.map φ *ᵥ B.map φ *ᵥ v
    rw [hP, Matrix.mulVec_mulVec]
  unfold jetLength
  rw [heq]
  refine (Submodule.finrank_mono (LinearMap.range_comp_le_range H L)).trans (L.finrank_range_le.trans_eq ?_)
  change Module.finrank K (r → Jet t k) = Fintype.card r * k
  rw [Module.finrank_pi_fintype]
  simp [jetFinrank']

/-- Equivalent codimension form of the all-node, all-precision exact profile. -/
theorem exists_clippedDefectProfile (P : Matrix n n K[X]) (hp : P.det ≠ 0) :
    ∃ a : n → K[X], (∀ i, a i ≠ 0) ∧ (∑ i, (a i).natDegree) = P.det.natDegree ∧
      ∀ (t : K) (k : ℕ), Fintype.card n * k - jetLength P t k =
        ∑ i, min k (rootMultiplicity t (a i)) := by
  obtain ⟨a,ha,hd,hl⟩ := exists_clippedProfile P hp
  refine ⟨a,ha,hd,fun t k => ?_⟩
  have hz : (∑ i, (k-min k (rootMultiplicity t (a i)))) +
      (∑ i, min k (rootMultiplicity t (a i))) = Fintype.card n * k := by
    rw [← Finset.sum_add_distrib]
    simp [Nat.sub_add_cancel (Nat.min_le_left _ _)]
  rw [hl]
  omega

end RankBudget