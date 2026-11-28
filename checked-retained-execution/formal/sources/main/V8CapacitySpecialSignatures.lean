import V8CapacitySymbolic
import V8CapacityNativeMatrix

/-! A1/J2: the actual symbolic Taylor features have exact monomial
signatures. This derives the source's disjoint-support assertion in
both characteristics, without assuming formal independence of features. -/
namespace V8CapacitySpecialSignatures
open scoped Polynomial Classical BigOperators
open Polynomial V8CapacityFeatures
open V8CapacitySymbolic V8CapacityNativeMatrix

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 900000

variable {O H : Type*} [CommRing O] [Fintype H]
variable {k : ℕ}

def termScalar (π : O) (r : Fin k) : O :=
  π^(if r.val=0 then 1 else 0)

def term (π : O) (i : H) (r : Fin k) : (MvPolynomial (Digits H k) O)[X] :=
  C (MvPolynomial.monomial (Finsupp.single (i,r) 1) (termScalar π r))*X^r.val

theorem coefficient_shift (π : O) (hk : 0<k) (i : H) (j : ℕ) :
    (shiftedPolynomial (MvPolynomial.C π) k (symInput (R:=O) k i)).coeff j =
      if hj : j<k then MvPolynomial.monomial (Finsupp.single (i,⟨j,hj⟩) 1)
        (termScalar π (⟨j,hj⟩ : Fin k)) else 0 := by
  cases j with
  | zero =>
    rw [dif_pos hk]
    simp only [shiftedPolynomial,Polynomial.coeff_add,Polynomial.coeff_C,
      Polynomial.coeff_X_mul_zero, add_zero, symInput, dif_pos hk, termScalar,if_true,pow_one]
    rw [MvPolynomial.X,MvPolynomial.C_mul_monomial,mul_one]
  | succ j =>
    simp only [shiftedPolynomial,Polynomial.coeff_add,Polynomial.coeff_C,Nat.succ_ne_zero,if_false,
      zero_add,Polynomial.coeff_X_mul,Polynomial.finset_sum_coeff,Polynomial.coeff_C_mul_X_pow]
    by_cases hj : j+1 < k
    · have hm : j∈Finset.range (k-1) := Finset.mem_range.mpr (by omega)
      rw [Finset.sum_eq_single_of_mem j hm (fun x _ hx => by simp [Ne.symm hx])]
      simp [symInput,hj,termScalar,MvPolynomial.X]
    · rw [dif_neg hj]
      apply Finset.sum_eq_zero
      intro r hr
      have hne : j≠r := by have hh := Finset.mem_range.mp hr; omega
      rw [if_neg hne]

theorem shifted_sum (π : O) (hk : 0<k) (i : H) :
    shiftedPolynomial (MvPolynomial.C π) k (symInput (R:=O) k i) =
      ∑ r : Fin k, term π i r := by
  apply Polynomial.ext
  intro j
  rw [coefficient_shift π hk,Polynomial.finset_sum_coeff]
  simp only [term,Polynomial.coeff_C_mul_X_pow]
  by_cases hj : j<k
  · rw [dif_pos hj, Finset.sum_eq_single_of_mem (⟨j,hj⟩ : Fin k) (Finset.mem_univ _)]
    · simp
    · intro r _ hne
      apply if_neg
      intro hh
      exact hne (Fin.ext hh.symm)
  · rw [dif_neg hj]
    symm
    apply Finset.sum_eq_zero
    intro r _
    apply if_neg
    intro hh
    exact hj (hh.symm ▸ r.isLt)

abbrev Occ (a : H → ℕ) := Σ i : H, Fin (a i)

def choiceExp {a : H → ℕ} (s : Finset (Occ a)) (c : Occ a → Fin k) :
    Digits H k →₀ ℕ :=
  ∑ u ∈ s, Finsupp.single (u.1,c u) 1

def choiceWeight {a : H → ℕ} (s : Finset (Occ a)) (c : Occ a → Fin k) : ℕ :=
  ∑ u ∈ s, (c u).val

def choiceZeros {a : H → ℕ} (s : Finset (Occ a)) (c : Occ a → Fin k) : ℕ :=
  ∑ u ∈ s, if (c u).val=0 then 1 else 0

theorem product_terms (π : O) (a : H → ℕ) (s : Finset (Occ a)) (c : Occ a → Fin k) :
    (∏ u ∈ s, term π u.1 (c u)) =
      C (MvPolynomial.monomial (choiceExp s c) (π^choiceZeros s c))*X^(choiceWeight s c) := by
  induction s using Finset.induction_on with
  | empty => simp [choiceExp,choiceZeros,choiceWeight]
  | @insert u s hu ih =>
    rw [Finset.prod_insert hu, ih]
    simp only [term,termScalar,choiceExp,choiceZeros,choiceWeight,Finset.sum_insert hu,pow_add]
    rw [← MvPolynomial.monomial_mul,Polynomial.C_mul]
    ring

theorem exact_choice_coeff (π : O) (hk : 0<k) (a : H → ℕ)
    (j : ℕ) (d : Digits H k →₀ ℕ) :
    (feature π k a j).coeff d =
      ∑ c : Occ a → Fin k, if j=choiceWeight Finset.univ c then
        if choiceExp Finset.univ c=d then π^choiceZeros Finset.univ c else 0 else 0 := by
  unfold feature rawFeature
  have hp :
      (∏ i : H, shiftedPolynomial (MvPolynomial.C π) k (symInput (R:=O) k i)^a i) =
      ∏ u : Occ a, shiftedPolynomial (MvPolynomial.C π) k (symInput (R:=O) k u.1) := by
    simp [Fintype.prod_sigma]
  rw [hp]
  simp_rw [shifted_sum π hk]
  rw [Fintype.prod_sum]
  simp_rw [product_terms π a]
  rw [Polynomial.finset_sum_coeff,MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro c _
  rw [Polynomial.coeff_C_mul_X_pow]
  by_cases hz : j=choiceWeight Finset.univ c
  · rw [if_pos hz,if_pos hz,MvPolynomial.coeff_monomial]
  · simp [hz]

def rowSum (d : Digits H k →₀ ℕ) (i : H) : ℕ :=
  ∑ r : Fin k, d (i,r)

def zWeight (d : Digits H k →₀ ℕ) : ℕ :=
  ∑ e : Digits H k, e.2.val*d e

theorem choice_rows (a : H → ℕ) (c : Occ a → Fin k) (i : H) :
    rowSum (choiceExp Finset.univ c) i=a i := by
  unfold rowSum choiceExp
  simp only [Finsupp.finset_sum_apply]
  rw [Finset.sum_comm]
  have hv (u : Occ a) :
      (∑ r : Fin k, (Finsupp.single (u.1,c u) (1:ℕ)) (i,r)) =
      if i=u.1 then 1 else 0 := by
    by_cases h : i=u.1
    · subst i
      rw [if_pos rfl, Finset.sum_eq_single_of_mem (c u) (Finset.mem_univ _)]
      · exact Finsupp.single_eq_same
      · intro x _ hx
        apply Finsupp.single_eq_of_ne
        intro he
        exact hx (congrArg Prod.snd he)
    · rw [if_neg h]
      apply Finset.sum_eq_zero
      intro x _
      apply Finsupp.single_eq_of_ne
      intro he
      exact h (congrArg Prod.fst he)
  simp_rw [hv]
  rw [Fintype.sum_sigma,Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
  · simp
  · intro x _ hx
    simp [Ne.symm hx]

theorem choice_zweight (a : H → ℕ) (c : Occ a → Fin k) :
    zWeight (choiceExp Finset.univ c)=choiceWeight Finset.univ c := by
  unfold zWeight choiceExp choiceWeight
  simp only [Finsupp.finset_sum_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_eq_single_of_mem (u.1,c u) (Finset.mem_univ _)]
  · rw [Finsupp.single_eq_same,mul_one]
  · intro x _ hx
    rw [Finsupp.single_eq_of_ne hx,mul_zero]

theorem recover_degree_signature (π : O) (hk : 0<k) (a : H → ℕ) (j : ℕ)
    (d : Digits H k →₀ ℕ) (h : (feature π k a j).coeff d≠0) :
    (∀ i, rowSum d i=a i) ∧ zWeight d=j := by
  rw [exact_choice_coeff π hk a j d] at h
  by_contra hn
  apply h
  apply Finset.sum_eq_zero
  intro c _
  split_ifs with hJ hD
  · exact False.elim (hn ⟨fun i => hD ▸ choice_rows a c i,hD ▸ (choice_zweight a c).trans hJ.symm⟩)
  · rfl
  · rfl

variable [IsDomain O]

/-- Literal boxed active features in A2 have disjoint monomial supports. -/
theorem actual_cols_disjoint (π : O) (P k : ℕ) (hk : 0<k) (i j : Box H P k)
    (d : Digits H k →₀ ℕ) (hi : (symCol π P k i).coeff d≠0)
    (hj : (symCol π P k j).coeff d≠0) : i=j := by
  unfold symCol at hi hj
  split_ifs at hi with h₁
  · split_ifs at hj with h₂
    · obtain ⟨g₁,t₁⟩ := recover_degree_signature π hk _ _ _ hi
      obtain ⟨g₂,t₂⟩ := recover_degree_signature π hk _ _ _ hj
      apply Prod.ext
      · funext e
        apply Fin.ext
        exact (g₁ e).symm.trans (g₂ e)
      · exact Fin.ext (t₁.symm.trans t₂)
    · exact False.elim (hj (by simp))
  · exact False.elim (hi (by simp))

#print axioms coefficient_shift
#print axioms shifted_sum
#print axioms product_terms
#print axioms exact_choice_coeff
#print axioms choice_rows
#print axioms choice_zweight
#print axioms recover_degree_signature
#print axioms actual_cols_disjoint
end
end V8CapacitySpecialSignatures

