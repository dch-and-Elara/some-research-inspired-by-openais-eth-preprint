import P5NativeEntryUnit
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.FieldTheory.Finiteness

/-! Literal source parity queries for signed-unit clauses (source lines
3218–3238, 3454–3466).  Lists of candidates are indexed by positions; distinct
lists representing one binary row are not identified with each other. -/
namespace Paper5.NativeEntry
open scoped BigOperators
open Module

abbrev Word (n : ℕ) := Fin n → F₂
abbrev Rows (n : ℕ) := List (Word n)
abbrev Candidate (n P : ℕ) := Fin P → Fin n × F₂

def candidateRow {n P : ℕ} (γ : Candidate n P) : Word n :=
  fun v => ∑ j : Fin P, if (γ j).1=v then (γ j).2 else 0

@[simp] theorem candidate_count (n P : ℕ) :
    Fintype.card (Candidate n P)=(2*n)^P := by
  simp [Candidate,Nat.mul_comm]

def singletonRow {n : ℕ} (v : Fin n) : Word n := fun w => if v=w then 1 else 0

def singletonList {n P : ℕ} (hP : 0<P) (v : Fin n) : Candidate n P :=
  fun j => (v,if j=(⟨0,hP⟩ : Fin P) then 1 else 0)

theorem singleton_represented {n P : ℕ} (hP : 0<P) (v : Fin n) :
    candidateRow (singletonList hP v)=singletonRow v := by
  funext w
  by_cases h : v=w
  · simp only [candidateRow,singletonList,h,if_true,singletonRow]
    simp
  · simp [candidateRow,singletonList,singletonRow,h]

def matrix {n : ℕ} (A : Rows n) : Matrix (Fin A.length) (Fin n) F₂ :=
  fun i => A.get i

noncomputable def rowForm {n : ℕ} (r : Word n) : Word n →ₗ[F₂] F₂ :=
  ∑ v : Fin n, r v • LinearMap.proj v

theorem rowForm_apply {n : ℕ} (r x : Word n) :
    rowForm r x=∑ v : Fin n,r v*x v := by
  simp [rowForm]

@[simp] theorem singleton_read {n : ℕ} (v : Fin n) (x : Word n) :
    rowForm (singletonRow v) x=x v := by
  simp [rowForm_apply,singletonRow,ite_mul]

noncomputable def kernel {n : ℕ} (A : Rows n) : Submodule F₂ (Word n) :=
  LinearMap.ker (matrix A).mulVecLin

theorem mem_kernel {n : ℕ} (A : Rows n) (x : Word n) :
    x∈kernel A ↔ ∀ r∈A, rowForm r x=0 := by
  rw [kernel,LinearMap.mem_ker]
  simp only [Matrix.mulVecLin_apply,funext_iff,Matrix.mulVec, dotProduct, matrix,
    Pi.zero_apply,rowForm_apply]
  constructor
  · intro h r rA
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp rA
    simpa only [hi] using h i
  · intro h i
    exact h _ (List.get_mem _ _)

theorem mem_kernel_append {n : ℕ} (A : Rows n) (r x : Word n) :
    x∈kernel (A++[r]) ↔ x∈kernel A ∧ rowForm r x=0 := by
  simp only [mem_kernel,List.mem_append,List.mem_singleton]
  constructor
  · intro h
    exact ⟨fun t ht=>h t (Or.inl ht),h r (Or.inr rfl)⟩
  · rintro ⟨h,hr⟩ t (ht|rfl)
    · exact h t ht
    · exact hr

noncomputable def nullity {n : ℕ} (A : Rows n) : ℕ := finrank F₂ (kernel A)

theorem rank_add_nullity {n : ℕ} (A : Rows n) :
    (matrix A).rank + nullity A = n := by
  simpa [Matrix.rank,nullity,kernel] using (matrix A).mulVecLin.finrank_range_add_finrank_ker

theorem rank_eq_full_iff {n : ℕ} (A : Rows n) :
    (matrix A).rank=n ↔ kernel A=⊥ := by
  have h := rank_add_nullity A
  have hf : nullity A=0 ↔ kernel A=⊥ := Submodule.finrank_eq_zero
  rw [←hf]
  omega

def sourceTest {n : ℕ} (r : Word n) (sgn x : Fin n → Bool) : F₂ :=
  ∑ v : Fin n, r v*unitViolation (asBit (sgn v)) (asBit (x v))

theorem source_test_formula {n : ℕ} (r : Word n) (sgn x : Fin n → Bool) :
    sourceTest r sgn x=rowForm r ((fun v=>asBit (x v)) + fun v=>asBit (sgn v)) := by
  simp [sourceTest,unit_violation_formula,rowForm_apply]

def Accepts {n : ℕ} (A : Rows n) (sgn x : Fin n → Bool) : Prop :=
  ∀ r∈A,sourceTest r sgn x=0

noncomputable def acceptedCount {n : ℕ} (A : Rows n) (sgn : Fin n → Bool) : ℕ :=
  Nat.card {x : Fin n → Bool // Accepts A sgn x}

noncomputable def translate {n : ℕ} (sgn : Fin n → Bool) : (Fin n → Bool) ≃ Word n :=
  (Equiv.piCongrRight (fun _=>bitEquiv)).trans (Equiv.addRight (fun v=>asBit (sgn v)))

noncomputable def solutionEquiv {n : ℕ} (A : Rows n) (sgn : Fin n → Bool) :
    {x : Fin n → Bool // Accepts A sgn x} ≃ kernel A := by
  apply Equiv.subtypeEquiv (translate sgn)
  intro x
  simp only [Accepts,source_test_formula,mem_kernel]
  rfl

theorem accepted_count_exact {n : ℕ} (A : Rows n) (sgn : Fin n → Bool) :
    acceptedCount A sgn=2^nullity A := by
  rw [acceptedCount,Nat.card_congr (solutionEquiv A sgn),Module.natCard_eq_pow_finrank (K:=F₂)]
  simp [nullity,Nat.card_eq_fintype_card]

theorem accepted_count_rank {n : ℕ} (A : Rows n) (sgn : Fin n → Bool) :
    acceptedCount A sgn=2^(n-(matrix A).rank) := by
  rw [accepted_count_exact]
  congr 1
  have h := rank_add_nullity A
  omega

theorem candidate_vector_sign_independent {n P : ℕ} (A : Rows n)
    (s s' : Fin n → Bool) :
    (fun γ : Candidate n P => acceptedCount (A++[candidateRow γ]) s) =
      fun γ => acceptedCount (A++[candidateRow γ]) s' := by
  funext γ
  simp [accepted_count_exact]

theorem kernel_append_le {n : ℕ} (A : Rows n) (r : Word n) :
    kernel (A++[r])≤kernel A := fun _ hx => (mem_kernel_append _ _ _).mp hx |>.1

noncomputable def restrict_form_append {n : ℕ} (A : Rows n) (r : Word n) :
    LinearMap.ker ((rowForm r).comp (kernel A).subtype) ≃ₗ[F₂] kernel (A++[r]) where
  toFun x := ⟨x.1.1,(mem_kernel_append _ _ _).2 ⟨x.1.2,x.2⟩⟩
  invFun x := ⟨⟨x.1,(mem_kernel_append _ _ _).mp x.2 |>.1⟩,
    (mem_kernel_append _ _ _).mp x.2 |>.2⟩
  left_inv _ := Subtype.ext (Subtype.ext rfl)
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

theorem nullity_append_bounds {n : ℕ} (A : Rows n) (r : Word n) :
    nullity A-1≤nullity (A++[r]) ∧ nullity (A++[r])≤nullity A := by
  let f := (rowForm r).comp (kernel A).subtype
  have hD := f.finrank_range_add_finrank_ker
  have he := (restrict_form_append A r).finrank_eq
  have hr : finrank F₂ (LinearMap.range f)≤1 := by simpa using (Submodule.finrank_le (LinearMap.range f))
  change finrank F₂ (LinearMap.ker f)=nullity (A++[r]) at he
  change finrank F₂ (LinearMap.range f)+finrank F₂ (LinearMap.ker f)=nullity A at hD
  refine ⟨by omega,Submodule.finrank_mono (kernel_append_le A r)⟩

theorem some_singleton_progress {n : ℕ} (A : Rows n) (h : 0<nullity A) :
    ∃ v : Fin n, nullity (A++[singletonRow v])+1=nullity A := by
  have hk : kernel A ≠ ⊥ := by
    intro hf
    have hz : nullity A=0 := Submodule.finrank_eq_zero.mpr hf
    omega
  have hpos : (⊥ : Submodule F₂ (Word n))<kernel A := bot_lt_iff_ne_bot.mpr hk
  obtain ⟨x,hx,hne⟩ := SetLike.exists_of_lt hpos
  have hx0 : x ≠ 0 := by simpa using hne
  obtain ⟨v,hv⟩ : ∃ v : Fin n,x v ≠ 0 := by
    by_contra! H
    exact hx0 (funext H)
  have hlt : kernel (A++[singletonRow v])<kernel A := by
    apply lt_of_le_of_ne (kernel_append_le _ _)
    intro he
    have hj := (mem_kernel_append A (singletonRow v) x).mp (he.symm ▸ hx)
    exact hv (by simpa using hj.2)
  have hdim := Submodule.finrank_lt_finrank_of_lt hlt
  have hlo := (nullity_append_bounds A (singletonRow v)).1
  change nullity (A++[singletonRow v])<nullity A at hdim
  exact ⟨v,by omega⟩

#print axioms candidate_count
#print axioms singleton_represented
#print axioms mem_kernel
#print axioms mem_kernel_append
#print axioms rank_add_nullity
#print axioms rank_eq_full_iff
#print axioms source_test_formula
#print axioms solutionEquiv
#print axioms accepted_count_exact
#print axioms accepted_count_rank
#print axioms candidate_vector_sign_independent
#print axioms kernel_append_le
#print axioms restrict_form_append
#print axioms nullity_append_bounds
#print axioms some_singleton_progress
end Paper5.NativeEntry