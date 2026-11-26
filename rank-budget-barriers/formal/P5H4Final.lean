import P5H4NormalRank
import P5H4Order

/-! The full normal-rank H4 formula, with actual ordered local exponents,
actual normalized determinants of minor ideals, and the upper grade bound
for every order s, including non-linear sampled irreducibles. -/
namespace P5H4
open Polynomial Matrix
open scoped BigOperators Classical

variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]

/-- One certificate binds all truncation orders to the same normal rank
and the same determinantal GCDs. Local exponents are ordered separately at
each sampled prime, retaining every multiplicity including ties. -/
structure GeneralProfile (A : Matrix m n K[X]) where
  normalRank : ℕ
  a : Fin normalRank → K[X]
  order : K[X] → Equiv.Perm (Fin normalRank)
  a_nonzero : ∀ i, a i ≠ 0
  sorted : ∀ f : K[X], Monotone (fun i => multiplicity f (a (order f i)))
  minor_support : ∀ s, determinantalGCD A s ≠ 0 ↔ s ≤ normalRank
  clipped : ∀ (f : K[X]), f.Monic → Irreducible f → ∀ k,
    normalRank*(f.natDegree*k) - quotientLength A (f^k) =
      f.natDegree * ∑ i, min k (multiplicity f (a (order f i)))
  divisor_order : ∀ s (hs : s ≤ normalRank) (f : K[X]), f.Monic → Irreducible f →
    multiplicity f (determinantalGCD A s) =
      ∑ i, multiplicity f (a (order f (Fin.castLE hs i)))

set_option maxHeartbeats 5500000 in
theorem general_profile (A : Matrix m n K[X]) : Nonempty (GeneralProfile A) := by
  obtain ⟨r,a,ha,himage,hsupp,hmin⟩ := normal_rank_same_chart A
  choose σ hσ using fun f : K[X] => sort_weights (fun i => multiplicity f (a i))
  refine ⟨⟨r,a,σ,ha,hσ,hsupp,?_,?_⟩⟩
  · intro f hm hf k
    rw [himage f hm hf k]
    have hsum :
        (∑ i, min k (multiplicity f (a i))) =
          ∑ i, min k (multiplicity f (a (σ f i))) :=
      (Fintype.sum_equiv (σ f) _ _ (fun _ => rfl)).symm
    have heq :
        (∑ i, f.natDegree*(k-min k (multiplicity f (a i)))) +
          f.natDegree * (∑ i, min k (multiplicity f (a i))) =
          r * (f.natDegree*k) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      simp [← Nat.mul_add, Nat.sub_add_cancel (min_le_left _ _)]
    rw [← hsum]
    omega
  · intro s h f hm hf
    obtain ⟨hlo,u,hu,he⟩ := hmin s h f hm hf
    obtain ⟨hprefix,v,hv,hv'⟩ := sorted_prefix_minimum h
      (fun i => multiplicity f (a i)) (σ f) (hσ f)
    exact le_antisymm ((hlo v hv).trans_eq hv'.symm) ((hprefix u hu).trans_eq he.symm)

omit [Fintype m] in
/-- The full first-s clipped sum is controlled by the degree of the
actual greatest common divisor of s-minors, and hence by s*d. -/
theorem general_partial_budget (A : Matrix m n K[X]) (P : GeneralProfile A)
    (s d : ℕ) (hs : s ≤ P.normalRank) (S : Finset K[X]) (k : K[X] → ℕ)
    (hm : ∀ f ∈ S, f.Monic) (hi : ∀ f ∈ S, Irreducible f)
    (hgrade : ∀ i j, (A i j).natDegree ≤ d) :
    (∑ f ∈ S, f.natDegree * ∑ i,
      min (k f) (multiplicity f (P.a (P.order f (Fin.castLE hs i))))) ≤
      (determinantalGCD A s).natDegree ∧ (determinantalGCD A s).natDegree ≤ s*d := by
  have hz := (P.minor_support s).mpr hs
  refine ⟨?_,detdiv_entry_grade A s d hz hgrade⟩
  calc
    _ ≤ ∑ f ∈ S, f.natDegree*multiplicity f (determinantalGCD A s) := by
      apply Finset.sum_le_sum
      intro f hf
      rw [P.divisor_order s hs f (hm f hf) (hi f hf)]
      exact Nat.mul_le_mul_left _ (Finset.sum_le_sum (fun i _ => min_le_right _ _))
    _ ≤ _ := irreducible_multiplicity_budget _ hz S hm hi

omit [Fintype m] [Fintype n] in
theorem linear_multiplicity (t : K) (p : K[X]) (hp : p ≠ 0) :
    multiplicity (X-C t) p = rootMultiplicity t p := by
  have hpositive : 0 < (X-C t : K[X]).natDegree := by simp
  have hfin := polynomial_finiteMultiplicity hpositive hp
  exact le_antisymm ((le_rootMultiplicity_iff hp).mpr (pow_multiplicity_dvd _ _))
    (hfin.le_multiplicity_of_pow_dvd (pow_rootMultiplicity_dvd p t))

omit [Fintype m] [Fintype n] in
theorem normalized_detdiv_monic (A : Matrix m n K[X]) (s : ℕ)
    (h : determinantalGCD A s ≠ 0) : (determinantalGCD A s).Monic := by
  unfold determinantalGCD at *
  apply Polynomial.monic_normalize
  intro h0
  exact h (by simp [h0])

#print axioms general_profile
#print axioms general_partial_budget
#print axioms linear_multiplicity
#print axioms normalized_detdiv_monic
end P5H4
