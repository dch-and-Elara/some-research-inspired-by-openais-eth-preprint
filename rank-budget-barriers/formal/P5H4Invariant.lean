import P5H4Final
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-! Recover the genuine global invariant factors as adjacent quotients
of determinantal gcds. Every local order is aligned with the same ordered
profile, and the divisibility ordering is separately certified. -/
namespace P5H4
open Polynomial Matrix UniqueFactorizationMonoid
open scoped BigOperators Classical

variable {K m n : Type*} [Field K]

theorem detdiv_step_dvd (A : Matrix m n K[X]) (s : ℕ) :
    determinantalGCD A s ∣ determinantalGCD A (s+1) := by
  have hr := (dvd_determinantalGCD_iff A s (determinantalGCD A s)).mp (dvd_refl _)
  apply (dvd_determinantalGCD_iff A (s+1) _).mpr
  intro u v
  rw [Matrix.det_succ_row_zero]
  apply Finset.dvd_sum
  intro j _
  have hminor :
      ((A.submatrix u v).submatrix Fin.succ j.succAbove) =
        A.submatrix (u∘Fin.succ) (v∘j.succAbove) := rfl
  rw [hminor,mul_comm]
  exact (hr _ _).trans (dvd_mul_right _ _)

/-- Checking true local exponents at monic irreducibles suffices for
polynomial divisibility; no choice of factorization is a premise. -/
theorem dvd_via_monic_orders (a b : K[X]) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ f : K[X], f.Monic → Irreducible f → multiplicity f a ≤ multiplicity f b) :
    a ∣ b := by
  apply (dvd_iff_normalizedFactors_le_normalizedFactors ha hb).mpr
  apply Multiset.le_iff_count.mpr
  intro f
  by_cases hf : f ∈ normalizedFactors a
  · have hprime : Prime f := prime_of_normalized_factor _ hf
    have hn : normalize f = f := normalize_normalized_factor _ hf
    have hm : f.Monic := hn ▸ Polynomial.monic_normalize hprime.ne_zero
    have hp : 0 < f.natDegree := by
      by_contra! hz
      exact hprime.not_unit (by
        rw [hm.natDegree_eq_zero.mp (Nat.eq_zero_of_le_zero hz)]
        exact isUnit_one)
    have hcount (z : K[X]) (hz : z ≠ 0) : (normalizedFactors z).count f = multiplicity f z := by
      have hv := emultiplicity_eq_count_normalizedFactors hprime.irreducible hz
      rw [hn,(polynomial_finiteMultiplicity hp hz).emultiplicity_eq_multiplicity] at hv
      exact_mod_cast hv.symm
    rw [hcount a ha,hcount b hb]
    exact h f hm hprime.irreducible
  · rw [Multiset.count_eq_zero.mpr hf]
    exact Nat.zero_le _

variable [Fintype m] [Fintype n]

omit [Fintype m] in
set_option maxHeartbeats 4200000 in
theorem invariant_factor_at (A : Matrix m n K[X]) (P : GeneralProfile A)
    (i : Fin P.normalRank) :
    ∃ g : K[X], g.Monic ∧ determinantalGCD A (i.val+1) = determinantalGCD A i.val * g ∧
      ∀ f : K[X], f.Monic → Irreducible f →
        multiplicity f g = multiplicity f (P.a (P.order f i)) := by
  let lo := determinantalGCD A i.val
  let hi := determinantalGCD A (i.val+1)
  have hlo : lo ≠ 0 := (P.minor_support _).2 i.isLt.le
  have hhi : hi ≠ 0 := (P.minor_support _).2 (Nat.succ_le_of_lt i.isLt)
  obtain ⟨g,hg⟩ := detdiv_step_dvd A i.val
  change hi = lo*g at hg
  have hgn : g ≠ 0 := by
    intro hz
    exact hhi (by simpa [hz] using hg)
  have hlm := normalized_detdiv_monic A i.val hlo
  have hhm := normalized_detdiv_monic A (i.val+1) hhi
  have hgm : g.Monic := by
    change g.leadingCoeff = 1
    have h := congrArg leadingCoeff hg
    change hi.leadingCoeff = (lo*g).leadingCoeff at h
    rw [leadingCoeff_mul,hlm,hhm,one_mul] at h
    exact h.symm
  refine ⟨g,hgm,hg,?_⟩
  intro f hm hf
  have hp : 0 < f.natDegree := by
    by_contra! hz
    exact hf.not_isUnit (by
      rw [hm.natDegree_eq_zero.mp (Nat.eq_zero_of_le_zero hz)]
      exact isUnit_one)
  have h₁ := P.divisor_order i.val i.isLt.le f hm hf
  have h₂ := P.divisor_order (i.val+1) (Nat.succ_le_of_lt i.isLt) f hm hf
  let w (j : Fin P.normalRank) := multiplicity f (P.a (P.order f j))
  change multiplicity f lo = ∑ j, w (Fin.castLE i.isLt.le j) at h₁
  change multiplicity f hi = ∑ j, w (Fin.castLE (Nat.succ_le_of_lt i.isLt) j) at h₂
  have hprefix : (∑ j, w (Fin.castLE (Nat.succ_le_of_lt i.isLt) j)) =
      (∑ j, w (Fin.castLE i.isLt.le j)) + w i := by
    rw [Fin.sum_univ_castSucc]
    congr 1
  have hgord : multiplicity f hi = multiplicity f lo + multiplicity f g := by
    rw [hg,multiplicity_mul hf.prime (polynomial_finiteMultiplicity hp (mul_ne_zero hlo hgn))]
  rw [hprefix,←h₁] at h₂
  change multiplicity f g = w i
  omega

omit [Fintype m] in
/-- The recovered monic invariant factors are globally divisibility
ordered and their local exponents equal those in the actual jet profile. -/
theorem invariant_factor_sequence (A : Matrix m n K[X]) (P : GeneralProfile A) :
    ∃ d : Fin P.normalRank → K[X], (∀ i, (d i).Monic) ∧
      (∀ i, determinantalGCD A (i.val+1) = determinantalGCD A i.val*d i) ∧
      (∀ i j, i ≤ j → d i ∣ d j) ∧
      ∀ i (f : K[X]), f.Monic → Irreducible f →
        multiplicity f (d i) = multiplicity f (P.a (P.order f i)) := by
  choose d hm sth hlocal using fun i => invariant_factor_at A P i
  refine ⟨d,hm,sth,?_,hlocal⟩
  intro i j h
  apply dvd_via_monic_orders _ _ (hm i).ne_zero (hm j).ne_zero
  intro f hf hp
  rw [hlocal i f hf hp,hlocal j f hf hp]
  exact P.sorted f h

#print axioms detdiv_step_dvd
#print axioms dvd_via_monic_orders
#print axioms invariant_factor_at
#print axioms invariant_factor_sequence
end P5H4
