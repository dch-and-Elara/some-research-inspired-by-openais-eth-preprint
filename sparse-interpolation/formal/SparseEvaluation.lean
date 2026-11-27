import McCoy
import Mathlib.Algebra.Polynomial.Eval.Degree

open Polynomial Matrix

namespace GrenetMcCoy

variable {R ι : Type*} [CommRing R]

/-- The columns of the evaluation matrix correspond to an allowed
exponent set, including exponents assigned coefficient zero. -/
def evaluationMatrix (x : ι → R) (E : Finset ℕ) : Matrix ι E R :=
  fun i e => x i ^ e.val

noncomputable def polynomialOn (E : Finset ℕ) (c : E → R) : R[X] :=
  ∑ j : E, monomial j.val (c j)

theorem coeff_polynomialOn (E : Finset ℕ) (c : E → R) (j : ℕ) :
    (polynomialOn E c).coeff j = if hj : j ∈ E then c ⟨j, hj⟩ else 0 := by
  classical
  rw [polynomialOn, finset_sum_coeff]
  split_ifs with hj
  · rw [Finset.sum_eq_single (⟨j, hj⟩ : E)]
    · exact coeff_monomial_same j _
    · intro k _ hk
      exact coeff_monomial_of_ne _ (fun he => hk (Subtype.ext he.symm))
    · simp
  · refine Finset.sum_eq_zero fun k _ => ?_
    exact coeff_monomial_of_ne _ (fun he => hj (he ▸ k.property))

theorem polynomialOn_support (E : Finset ℕ) (c : E → R) :
    (polynomialOn E c).support ⊆ E := by
  intro j hj
  by_contra h
  exact (mem_support_iff.mp hj) (by simp [coeff_polynomialOn, h])

theorem polynomialOn_injective (E : Finset ℕ) :
    Function.Injective (polynomialOn (R := R) E) := by
  intro a b h
  funext j
  have hj := congrArg (fun p : R[X] => p.coeff j.val) h
  simpa [coeff_polynomialOn, j.property] using hj

theorem polynomialOn_eq (E : Finset ℕ) (p : R[X]) (hp : p.support ⊆ E) :
    polynomialOn E (fun j => p.coeff j.val) = p := by
  ext j
  by_cases hj : j ∈ E
  · simp [coeff_polynomialOn, hj]
  · have hzero : p.coeff j = 0 := notMem_support_iff.mp (fun h => hj (hp h))
    simp [coeff_polynomialOn, hj, hzero]

theorem evaluationMatrix_mulVec (x : ι → R) (E : Finset ℕ) (c : E → R) (i : ι) :
    ((evaluationMatrix x E) *ᵥ c) i = (polynomialOn E c).eval (x i) := by
  change (∑ j : E, x i ^ j.val * c j) = evalRingHom (x i) (∑ j : E, monomial j.val (c j))
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  change x i ^ j.val * c j = (monomial j.val (c j)).eval (x i)
  rw [eval_monomial, mul_comm]

/-- Two arbitrary polynomials whose supports are contained in the same
allowed set have distinct sample vectors unless they are equal. -/
def DeterminesOn (x : ι → R) (E : Finset ℕ) : Prop :=
  ∀ f g : R[X], f.support ⊆ E → g.support ⊆ E →
    (∀ i, f.eval (x i) = g.eval (x i)) → f = g

theorem determinesOn_iff_evaluationMatrix_injective (x : ι → R) (E : Finset ℕ) :
    DeterminesOn x E ↔ Function.Injective (evaluationMatrix x E).mulVec := by
  constructor
  · intro h a b he
    apply polynomialOn_injective E
    refine h _ _ (polynomialOn_support E a) (polynomialOn_support E b) fun i => ?_
    simpa only [evaluationMatrix_mulVec] using congrFun he i
  · intro h f g hf hg he
    let a : E → R := fun j => f.coeff j.val
    let b : E → R := fun j => g.coeff j.val
    have ha : polynomialOn E a = f := polynomialOn_eq E f hf
    have hb : polynomialOn E b = g := polynomialOn_eq E g hg
    have hab : a = b := h (funext fun i => by
      rw [evaluationMatrix_mulVec, evaluationMatrix_mulVec, ha, hb, he])
    rw [← ha, ← hb, hab]

theorem determinesOn_iff_annihilator_eq_bot (x : ι → R) (E : Finset ℕ) :
    DeterminesOn x E ↔ (fullMinorIdeal (evaluationMatrix x E)).annihilator = ⊥ :=
  (determinesOn_iff_evaluationMatrix_injective x E).trans
    (mulVec_injective_iff_fullMinorIdeal_annihilator_eq_bot _)

/-- At most t nonzero coefficients, including the zero polynomial. -/
def Admissible (d t : ℕ) (p : R[X]) : Prop :=
  p.natDegree ≤ d ∧ p.support.card ≤ t

private theorem support_sub_subset (p q : R[X]) : (p - q).support ⊆ p.support ∪ q.support := by
  intro j hj
  by_contra h
  rw [Finset.mem_union, not_or] at h
  exact (mem_support_iff.mp hj) (by simp [coeff_sub, notMem_support_iff.mp h.1,
    notMem_support_iff.mp h.2])

private theorem admissible_of_support_subset {p : R[X]} {E : Finset ℕ} {d t : ℕ}
    (hp : p.support ⊆ E) (hE : E ⊆ Finset.range (d + 1)) (hcard : E.card ≤ t) :
    Admissible d t p :=
  ⟨natDegree_le_iff_coeff_eq_zero.mpr (fun _ hj => notMem_support_iff.mp fun h =>
    (not_lt_of_ge (Nat.succ_le_of_lt hj)) (Finset.mem_range.mp (hE (hp h)))),
    (Finset.card_le_card hp).trans hcard⟩

theorem admissible_sub {d t : ℕ} {f g : R[X]}
    (hf : Admissible d t f) (hg : Admissible d t g) :
    Admissible d (2 * t) (f - g) :=
  ⟨by simpa using natDegree_sub_le_of_le hf.1 hg.1, calc
    _ ≤ (f.support ∪ g.support).card := Finset.card_le_card (support_sub_subset f g)
    _ ≤ f.support.card + g.support.card := Finset.card_union_le _ _
    _ ≤ 2 * t := by have := hf.2; have := hg.2; omega⟩

/-- Every degree-bounded 2t-sparse polynomial is a difference of two
degree-bounded t-sparse polynomials, over the same ring. -/
theorem admissible_iff_split {d t : ℕ} (p : R[X]) :
    Admissible d (2 * t) p ↔
      ∃ f g : R[X], Admissible d t f ∧ Admissible d t g ∧ p = f - g := by
  refine ⟨?_, ?_⟩
  · rintro ⟨hdeg, hcard⟩
    let S := p.support
    obtain ⟨U, hU, hUc⟩ := Finset.exists_subset_card_eq (s := S) (min_le_left S.card t)
    let V := S \ U
    have hV : V ⊆ S := Finset.sdiff_subset
    have hSc : S.card ≤ 2 * t := hcard
    have hVc : V.card ≤ t := by
      rw [Finset.card_sdiff_of_subset hU, hUc]
      omega
    have hS : S ⊆ Finset.range (d + 1) := supp_subset_range (Nat.lt_succ_of_le hdeg)
    let f := polynomialOn U (fun j => p.coeff j.val)
    let g := polynomialOn V (fun j => -p.coeff j.val)
    refine ⟨f, g,
      admissible_of_support_subset (polynomialOn_support _ _) (hU.trans hS)
        (hUc ▸ min_le_right S.card t),
      admissible_of_support_subset (polynomialOn_support _ _) (hV.trans hS) hVc, ?_⟩
    ext j
    change p.coeff j =
      (polynomialOn U (fun j => p.coeff j.val) -
        polynomialOn V (fun j => -p.coeff j.val)).coeff j
    rw [coeff_sub, coeff_polynomialOn, coeff_polynomialOn]
    by_cases hj : j ∈ U
    · simp [hj, V]
    · by_cases hmem : j ∈ p.support
      · simp [hj, V, S, hmem]
      · have hz : p.coeff j = 0 := notMem_support_iff.mp hmem
        simp [hj, V, S, hmem, hz]
  · rintro ⟨f, g, hf, hg, rfl⟩
    exact admissible_sub hf hg

def DeterminesSparse (x : ι → R) (d t : ℕ) : Prop :=
  ∀ f g : R[X], Admissible d t f → Admissible d t g →
    (∀ i, f.eval (x i) = g.eval (x i)) → f = g

theorem determinesSparse_iff_no_sparse_kernel (x : ι → R) (d t : ℕ) :
    DeterminesSparse x d t ↔
      ∀ p : R[X], Admissible d (2 * t) p → (∀ i, p.eval (x i) = 0) → p = 0 := by
  constructor
  · intro h p hp hs
    obtain ⟨f, g, hf, hg, rfl⟩ := (admissible_iff_split p).mp hp
    rw [h f g hf hg (fun i => sub_eq_zero.mp (by simpa only [eval_sub] using hs i)),
      sub_self]
  · intro h f g hf hg hs
    exact sub_eq_zero.mp (h (f - g) (admissible_sub hf hg) fun i => by rw [eval_sub, hs i, sub_self])

/-- Equivalent criterion over every allowed column set of size ≤ 2t. -/
theorem determinesSparse_iff_support_matrices (x : ι → R) (d t : ℕ) :
    DeterminesSparse x d t ↔
      ∀ E : Finset ℕ, E ⊆ Finset.range (d + 1) → E.card ≤ 2 * t →
        Function.Injective (evaluationMatrix x E).mulVec := by
  rw [determinesSparse_iff_no_sparse_kernel]
  constructor
  · intro h E hE hcard
    apply (determinesOn_iff_evaluationMatrix_injective x E).mp
    intro f g hf hg hs
    apply sub_eq_zero.mp
    have hp := (support_sub_subset f g).trans (Finset.union_subset hf hg)
    exact h _ (admissible_of_support_subset hp hE hcard) fun i => by rw [eval_sub, hs i, sub_self]
  · intro h p hp hs
    have hinj := h p.support (supp_subset_range (Nat.lt_succ_of_le hp.1)) hp.2
    exact (determinesOn_iff_evaluationMatrix_injective x p.support).mpr hinj p 0
      (Finset.Subset.refl _) (by simp) fun i => by simpa only [eval_zero] using hs i

/-- It suffices to check the largest allowed exponent sets. Smaller allowed
supports extend to one of these sets by allowing extra zero coefficients. -/
theorem determinesSparse_iff_max_support_matrices (x : ι → R) (d t : ℕ) :
    DeterminesSparse x d t ↔
      ∀ E : Finset ℕ, E ⊆ Finset.range (d + 1) → E.card = min (2 * t) (d + 1) →
        Function.Injective (evaluationMatrix x E).mulVec := by
  rw [determinesSparse_iff_support_matrices]
  constructor
  · intro h E hE hEc
    exact h E hE (hEc ▸ min_le_left _ _)
  · intro h E hE hEc
    have he : E.card ≤ min (2 * t) (d + 1) :=
      le_min hEc (by simpa using Finset.card_le_card hE)
    have hb : min (2 * t) (d + 1) ≤ (Finset.range (d + 1)).card := by simp
    obtain ⟨T, hET, hT, hTc⟩ := Finset.exists_subsuperset_card_eq hE he hb
    apply (determinesOn_iff_evaluationMatrix_injective x E).mp
    intro f g hf hg hs
    exact (determinesOn_iff_evaluationMatrix_injective x T).mpr (h T hT hTc)
      f g (hf.trans hET) (hg.trans hET) hs

/-- Grenet 10.3, the full-column determinantal-ideal criterion, for exact
same-ring evaluations and degree-bounded sparse formal polynomials. -/
theorem determinesSparse_iff_determinantal_annihilator (x : ι → R) (d t : ℕ) :
    DeterminesSparse x d t ↔
      ∀ E : Finset ℕ, E ⊆ Finset.range (d + 1) → E.card = min (2 * t) (d + 1) →
        (fullMinorIdeal (evaluationMatrix x E)).annihilator = ⊥ := by
  simp_rw [← mulVec_injective_iff_fullMinorIdeal_annihilator_eq_bot]
  exact determinesSparse_iff_max_support_matrices x d t

/-- A failed support test supplies an actual pair of distinct admissible
inputs with identical same-ring observations. -/
theorem exists_sparse_collision_of_nonzero_minor_annihilator
    (x : ι → R) (E : Finset ℕ) {d t : ℕ}
    (hE : E ⊆ Finset.range (d + 1)) (hcard : E.card ≤ 2 * t)
    (r : R) (hr : r ≠ 0) (hkill : r ∈ (fullMinorIdeal (evaluationMatrix x E)).annihilator) :
    ∃ f g : R[X], Admissible d t f ∧ Admissible d t g ∧
      f ≠ g ∧ ∀ i, f.eval (x i) = g.eval (x i) := by
  obtain ⟨c, hc, hzero⟩ := exists_kernel_of_kills_full_minors (evaluationMatrix x E) r hr
    ((mem_fullMinorIdeal_annihilator _ r).mp hkill)
  let p := polynomialOn E c
  have hp : p ≠ 0 := by
    intro he
    have hz : polynomialOn E (0 : E → R) = 0 := by simp [polynomialOn]
    exact hc (polynomialOn_injective E (he.trans hz.symm))
  have ho (i : ι) : p.eval (x i) = 0 := by
    change (polynomialOn E c).eval (x i) = 0
    rw [← evaluationMatrix_mulVec, hzero]
    rfl
  obtain ⟨f, g, hf, hg, hdiff⟩ := (admissible_iff_split p).mp
    (admissible_of_support_subset (polynomialOn_support E c) hE hcard)
  refine ⟨f, g, hf, hg, ?_, ?_⟩
  · intro hfg
    exact hp (by rw [hdiff, hfg, sub_self])
  · intro i
    exact sub_eq_zero.mp (by simpa only [hdiff, eval_sub] using ho i)

end GrenetMcCoy
