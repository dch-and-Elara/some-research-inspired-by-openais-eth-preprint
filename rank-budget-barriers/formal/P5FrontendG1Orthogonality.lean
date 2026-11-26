import P5FrontendG1Quadratic

/-! Exact orthogonality of the actual finite-field parity tests.  Division
by the size of the row-index cube is only used as an integer cancellation
after obtaining an honest divisibility. -/
namespace Paper5.FrontendG1
open scoped BigOperators

theorem scalar_phase_sum : ∀ b : F₂,
    (∑ a : F₂,phase (a*b))=if b=0 then (2:ℤ) else 0 := by decide

theorem all_weight_orthogonality {I : Type*} [Fintype I] [DecidableEq I] (p : I→F₂) :
    (∑ a : I→F₂,phase (∑ i,a i*p i))=
      if ∀ i,p i=0 then (2:ℤ)^Fintype.card I else 0 := by
  classical
  simp_rw [phase_sum]
  have he : (∑ a : I→F₂,∏ i,phase (a i*p i)) =
      ∏ i : I,∑ a : F₂,phase (a*p i) :=
    (Fintype.prod_sum (fun i (a : F₂)=>phase (a*p i))).symm
  rw [he]
  simp_rw [scalar_phase_sum]
  by_cases h : ∀ i,p i=0
  · rw [if_pos h]
    simp [h]
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i,hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

noncomputable def zeroCount {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (P : I→Quad V) : ℕ :=
  (Finset.univ.filter fun x : Finset V=>∀ i,(P i).eval x=0).card

theorem orthogonality_counts {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (P : I→Quad V) :
    (2:ℤ)^Fintype.card I*(zeroCount P:ℤ)=∑ a : I→F₂,walsh (combine P a) := by
  classical
  unfold walsh zeroCount
  simp_rw [eval_combine]
  rw [Finset.sum_comm]
  simp_rw [all_weight_orthogonality]
  rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
  ring

theorem zero_count_divisible {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (N : ℕ) (hV : Fintype.card V=2*N) (P : I→Quad V) :
    (2:ℕ)^(N-Fintype.card I) ∣ zeroCount P := by
  let h := Fintype.card I
  by_cases hH : h≤N
  · have hd : (2:ℤ)^N ∣ (2:ℤ)^h*(zeroCount P:ℤ) := by
      rw [orthogonality_counts]
      apply Finset.dvd_sum
      intro a _
      exact quadratic_walsh_divisible (combine P a) N hV
    obtain ⟨u,hu⟩ := hd
    have hpow : (2:ℤ)^N=(2:ℤ)^h*(2:ℤ)^(N-h) := by rw [←pow_add,Nat.add_sub_of_le hH]
    rw [hpow,mul_assoc] at hu
    have hne : (2:ℤ)^h≠0 := by positivity
    have hd' : (2:ℤ)^(N-h) ∣ (zeroCount P:ℤ) := ⟨u,mul_left_cancel₀ hne hu⟩
    exact_mod_cast hd'
  · have hzero : N-Fintype.card I=0 := by change N-h=0; omega
    simp [hzero]

#print axioms scalar_phase_sum
#print axioms all_weight_orthogonality
#print axioms orthogonality_counts
#print axioms zero_count_divisible
end Paper5.FrontendG1