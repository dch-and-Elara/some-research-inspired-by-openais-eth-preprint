import P5FrontendG1TannerIncidence

/-! Literal finite checking of the source's Walsh-bias and local-distance
search predicates. No in-Lean claim of the Hoeffding/union-bound existence,
or of a running time for that exhaustive search, is made. -/
namespace Paper5.FrontendG1.Tanner
open scoped BigOperators

def sourceWalsh {ell d : ℕ} (s : Fin d→Word ell) (b : Word ell) : ℤ :=
  ∑ j, if dotProduct b (s j)=0 then (1:ℤ) else -1

def biasDenom (B m : ℕ) : ℕ := 200*B*sourceMu m

def biasViolations (B m : ℕ) (s : Fin (sourceDegree B m)→Word (sourceEll B m)) :
    Finset (Word (sourceEll B m)) :=
  Finset.univ.filter fun b =>
    b≠0 ∧ sourceDegree B m<(sourceWalsh s b).natAbs*biasDenom B m

def SourceBias (B m : ℕ) (s : Fin (sourceDegree B m)→Word (sourceEll B m)) : Prop :=
  ∀ b : Word (sourceEll B m),b≠0 →
    ((sourceWalsh s b).natAbs:ℚ)≤1/(biasDenom B m:ℚ)*(sourceDegree B m:ℚ)

theorem biasViolations_empty_exact {B m : ℕ} (hB : 0<B)
    (s : Fin (sourceDegree B m)→Word (sourceEll B m)) :
    biasViolations B m s=∅ ↔ SourceBias B m s := by
  have hd : 0<biasDenom B m := by unfold biasDenom sourceMu; positivity
  have hdq : (0:ℚ)<biasDenom B m := by exact_mod_cast hd
  have eq (b : Word (sourceEll B m)) :
      ((sourceWalsh s b).natAbs:ℚ)≤1/(biasDenom B m:ℚ)*(sourceDegree B m:ℚ) ↔
        (sourceWalsh s b).natAbs*biasDenom B m≤sourceDegree B m := by
    rw [one_div_mul_eq_div,le_div_iff₀ hdq]
    exact_mod_cast Iff.rfl
  rw [Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h b hBz
    apply (eq b).mpr
    apply Nat.le_of_not_gt
    intro hh
    exact h b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hBz,hh⟩)
  · intro h b hh
    obtain ⟨_,hb,hbad⟩ := Finset.mem_filter.mp hh
    exact (not_lt_of_ge ((eq b).mp (h b hb))) hbad

theorem q_one_has_no_bias_test {B m : ℕ} (hq : sourceQ B m=1)
    (s : Fin (sourceDegree B m)→Word (sourceEll B m)) : biasViolations B m s=∅ := by
  have ho : sourceEll B m=0 := by
    by_contra! h
    have hpow : (2:ℕ)^1≤2^(sourceEll B m) :=
      Nat.pow_le_pow_right (by decide) (by omega)
    unfold sourceQ at hq
    omega
  have hb (b : Word (sourceEll B m)) : b=0 := by
    funext j
    exact (Nat.not_lt_zero _ (j.isLt.trans_le ho.le)).elim
  rw [Finset.eq_empty_iff_forall_notMem]
  intro b hh
  exact (Finset.mem_filter.mp hh).2.1 (hb b)

def localViolations {c d : ℕ} (A : Matrix (Fin c) (Fin d) F₂) (D : ℚ) :
    Finset (Fin d→F₂) :=
  Finset.univ.filter fun v=>v≠0 ∧ A.mulVec v=0 ∧ (weight v:ℚ)<D

theorem localViolations_empty_exact {c d : ℕ} (A : Matrix (Fin c) (Fin d) F₂) (D : ℚ) :
    localViolations A D=∅ ↔ LocalDistance A D := by
  rw [Finset.eq_empty_iff_forall_notMem]
  constructor
  · intro h x hn hx
    apply le_of_not_gt
    intro he
    exact h x (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn,hx,he⟩)
  · intro h x hx
    obtain ⟨_,hn,he,hLt⟩ := Finset.mem_filter.mp hx
    exact (not_lt_of_ge (h x hn he)) hLt

def checkedInput {C : Type*} [Fintype C] {B : ℕ}
    (s : Fin (sourceDegree B (Fintype.card C))→Word (sourceEll B (Fintype.card C)))
    (A : Matrix (Fin (sourceLocalRows B (Fintype.card C))) (Fin (sourceDegree B (Fintype.card C))) F₂)
    (keep : C↪PrintEdges B (Fintype.card C))
    (h : localViolations A (sourceMinDistance B (Fintype.card C))=∅) :
    PrintedInput C B := ⟨s,A,keep,(localViolations_empty_exact A _).mp h⟩

theorem checkedInput_exact {C : Type*} [Fintype C] {B : ℕ}
    (s : Fin (sourceDegree B (Fintype.card C))→Word (sourceEll B (Fintype.card C)))
    (A : Matrix (Fin (sourceLocalRows B (Fintype.card C))) (Fin (sourceDegree B (Fintype.card C))) F₂)
    (keep : C↪PrintEdges B (Fintype.card C))
    (h : localViolations A (sourceMinDistance B (Fintype.card C))=∅) :
    (checkedInput s A keep h).initial=shortened s A keep := rfl

#print axioms biasViolations_empty_exact
#print axioms q_one_has_no_bias_test
#print axioms localViolations_empty_exact
#print axioms checkedInput_exact
end Paper5.FrontendG1.Tanner