import P5H4Irreducible

/-! Unimodular transport for actual quotient images, and the weighted
degree budget for any distinct monic irreducible sample factors. -/
namespace P5H4
open Polynomial Matrix Module
open scoped Classical BigOperators

variable {K i j l : Type*} [Field K] [Fintype i] [Fintype j] [Fintype l]

omit [Fintype i] in
theorem quotientMul_comp (A : Matrix i j K[X]) (B : Matrix j l K[X]) (q : K[X]) :
    quotientMul (A*B) q = (quotientMul A q).comp (quotientMul B q) := by
  apply LinearMap.ext
  intro x
  change (A*B).map (AdjoinRoot.mk q) *ᵥ x =
    A.map (AdjoinRoot.mk q) *ᵥ (B.map (AdjoinRoot.mk q) *ᵥ x)
  rw [Matrix.map_mul,Matrix.mulVec_mulVec]

omit [Fintype i] in
theorem quotientLength_mul_le (A : Matrix i j K[X]) (B : Matrix j l K[X]) (q : K[X])
    (hq : q.Monic) :
    quotientLength (A*B) q ≤ quotientLength A q ∧
      quotientLength (A*B) q ≤ quotientLength B q := by
  letI : Module.Finite K (AdjoinRoot q) := hq.finite_adjoinRoot
  unfold quotientLength
  rw [quotientMul_comp]
  refine ⟨Submodule.finrank_mono (LinearMap.range_comp_le_range _ _),?_⟩
  rw [LinearMap.range_comp]
  exact Submodule.finrank_map_le _ _

private theorem quotientLength_sandwich_le (A : Matrix i j K[X])
    (U : Matrix i i K[X]) (V : Matrix j j K[X]) (q : K[X]) (hq : q.Monic) :
    quotientLength (U*A*V) q ≤ quotientLength A q :=
  (quotientLength_mul_le (U*A) V q hq).1.trans (quotientLength_mul_le U A q hq).2

variable [DecidableEq i] [DecidableEq j]

theorem quotientLength_unimodular (A : Matrix i j K[X])
    (U : Matrix i i K[X]) (V : Matrix j j K[X]) (hu : IsUnit U) (hv : IsUnit V)
    (q : K[X]) (hq : q.Monic) : quotientLength (U*A*V) q = quotientLength A q := by
  obtain ⟨u,rfl⟩ := hu
  obtain ⟨v,rfl⟩ := hv
  have he : u.inv*(u.val*A*v.val)*v.inv = A := by
    calc
      _ = ((u.inv*u.val)*A)*(v.val*v.inv) := by simp only [Matrix.mul_assoc]
      _ = A := by rw [u.inv_val,v.val_inv,Matrix.one_mul,Matrix.mul_one]
  refine le_antisymm (quotientLength_sandwich_le A u.val v.val q hq) ?_
  have h := quotientLength_sandwich_le (u.val*A*v.val) u.inv v.inv q hq
  rwa [he] at h

/-- A monic irreducible polynomial that divides another monic irreducible
has the same degree and is exactly equal, so distinct factors are coprime. -/
theorem monic_irreducible_coprime {a b : K[X]} (ha : a.Monic) (hb : b.Monic)
    (ha' : Irreducible a) (hb' : Irreducible b) (hne : a ≠ b) : IsCoprime a b := by
  apply ha'.coprime_iff_not_dvd.mpr
  intro hd
  obtain ⟨c,hc⟩ := hd
  have hu : IsUnit c := (hb'.isUnit_or_isUnit hc).resolve_left ha'.not_isUnit
  have hdeg : b.natDegree ≤ a.natDegree := by
    rw [hc, natDegree_mul ha.ne_zero hu.ne_zero, natDegree_eq_zero_of_isUnit hu,add_zero]
  exact hne (eq_of_monic_of_dvd_of_natDegree_le ha hb ⟨c,hc⟩ hdeg).symm

theorem irreducible_multiplicity_budget (p : K[X]) (hp : p ≠ 0) (s : Finset K[X])
    (hmon : ∀ f ∈ s, f.Monic) (hirr : ∀ f ∈ s, Irreducible f) :
    (∑ f ∈ s, f.natDegree * multiplicity f p) ≤ p.natDegree := by
  let P := ∏ f ∈ s, f^(multiplicity f p)
  have hP : P ∣ p := by
    refine Finset.prod_dvd_of_coprime (fun a ha b hb hne => ?_) fun f _ => ?_
    · exact (monic_irreducible_coprime (hmon a ha) (hmon b hb) (hirr a ha) (hirr b hb) hne).pow
    · exact pow_multiplicity_dvd f p
  have hn : P.natDegree = ∑ f ∈ s, f.natDegree*multiplicity f p := by
    dsimp [P]
    rw [natDegree_prod_of_monic s _ (fun f hf => (hmon f hf).pow _)]
    simp only [natDegree_pow, Nat.mul_comm]
  rw [← hn]
  exact natDegree_le_of_dvd hP hp

set_option maxHeartbeats 3800000 in
/-- With one witness for all factors, the weighted actual image defect is
clipped at each sample, and the sum of such defects is bounded by det degree. -/
theorem irreducible_square_profile (A : Matrix i i K[X]) (hA : A.det ≠ 0) :
    ∃ a : i → K[X], (∀ i, a i ≠ 0) ∧
      (∀ (f : K[X]), f.Monic → Irreducible f → ∀ k,
        Fintype.card i * (f.natDegree*k) - quotientLength A (f^k) =
          f.natDegree * ∑ i, min k (multiplicity f (a i))) ∧
      ∀ (s : Finset K[X]) (k : K[X] → ℕ),
        (∀ f ∈ s, f.Monic) → (∀ f ∈ s, Irreducible f) →
        (∑ f ∈ s, (Fintype.card i * (f.natDegree*k f) - quotientLength A (f^k f)))
          ≤ A.det.natDegree := by
  obtain ⟨U,V,a,hU,hV,hdiag⟩ := RankBudget.polyDiagonalize A hA
  obtain ⟨ha,hdeg⟩ := RankBudget.diagonalDegree A U V a hA hU hV hdiag
  have hprofile (f : K[X]) (hm : f.Monic) (hf : Irreducible f) (k : ℕ) :
      Fintype.card i * (f.natDegree*k) - quotientLength A (f^k) =
        f.natDegree * ∑ i, min k (multiplicity f (a i)) := by
    rw [← quotientLength_unimodular A U V hU hV _ (hm.pow k),hdiag,
      irreducible_diagonal_length f hm hf a ha k]
    have hsc :
        (∑ i, f.natDegree*(k-min k (multiplicity f (a i)))) +
          f.natDegree * (∑ i, min k (multiplicity f (a i))) =
          Fintype.card i * (f.natDegree*k) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      simp [← Nat.mul_add, Nat.sub_add_cancel (min_le_left _ _)]
    omega
  refine ⟨a,ha,hprofile,fun s k hm hi => ?_⟩
  calc
    _ = ∑ f ∈ s, ∑ i, f.natDegree * min (k f) (multiplicity f (a i)) := by
      apply Finset.sum_congr rfl
      intro f hf
      rw [hprofile f (hm f hf) (hi f hf),Finset.mul_sum]
    _ ≤ ∑ f ∈ s, ∑ i, f.natDegree * multiplicity f (a i) :=
      Finset.sum_le_sum (fun f _ => Finset.sum_le_sum (fun i _ =>
        Nat.mul_le_mul_left _ (min_le_right _ _)))
    _ = ∑ i, ∑ f ∈ s, f.natDegree * multiplicity f (a i) := Finset.sum_comm
    _ ≤ ∑ i, (a i).natDegree := Finset.sum_le_sum (fun i _ =>
      irreducible_multiplicity_budget (a i) (ha i) s hm hi)
    _ = _ := hdeg

#print axioms quotientLength_unimodular
#print axioms irreducible_multiplicity_budget
#print axioms irreducible_square_profile
end P5H4
