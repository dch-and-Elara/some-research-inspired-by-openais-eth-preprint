import P5FrontendG1Orthogonality
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! The number h in the valuation bound is the genuine binary rank of
the original hash matrix. We select distinct original indexed rows;
duplicate rows therefore cannot artificially increase h. -/
namespace Paper5.FrontendG1
open scoped BigOperators
open Matrix Module

variable {R C : Type*} [Fintype R] [Fintype C]

theorem exists_indexed_row_basis (A : Matrix R C F₂) :
    ∃ e : Fin A.rank ↪ R,
      LinearIndependent F₂ (fun i=>A.row (e i)) ∧
      Submodule.span F₂ (Set.range fun i=>A.row (e i))=
        Submodule.span F₂ (Set.range A.row) := by
  classical
  obtain ⟨J,a,hInj,hSp,hLin⟩ := exists_linearIndependent' F₂ A.row
  letI : Finite J := Finite.of_injective a hInj
  letI : Fintype J := Fintype.ofFinite J
  have hc : Fintype.card J=A.rank := by
    rw [Matrix.rank_eq_finrank_span_row,←hSp]
    exact (finrank_span_eq_card hLin).symm
  let ef : Fin A.rank ≃ J := (Fintype.equivFinOfCardEq hc).symm
  let b : Fin A.rank ↪ R := ⟨a ∘ ef,hInj.comp ef.injective⟩
  refine ⟨b,hLin.comp _ ef.injective,?_⟩
  have hr : Set.range (fun i=>A.row (b i))=Set.range (A.row ∘ a) := by
    ext z
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨ef i,rfl⟩
    · rintro ⟨j,rfl⟩
      obtain ⟨i,hi⟩ := ef.surjective j
      exact ⟨i,by change A.row (a (ef i))=A.row (a j); rw [hi]⟩
  rw [hr,hSp]

omit [Fintype R] in
noncomputable def rowRead (z : C→F₂) : (C→F₂)→ₗ[F₂] F₂ :=
  ∑ c : C,z c • LinearMap.proj c

omit [Fintype R] in
theorem row_read_value (z b : C→F₂) : rowRead z b=∑ c,b c*z c := by
  simp [rowRead,mul_comm]

omit [Fintype R] in
theorem original_rows_equivalent {J : Type*} (A : Matrix R C F₂) (e : J→R)
    (hSp : Submodule.span F₂ (Set.range fun i=>A.row (e i))=
      Submodule.span F₂ (Set.range A.row)) (z : C→F₂) :
    A.mulVec z=0 ↔ ∀ i,rowRead z (A.row (e i))=0 := by
  have hEval (j : R) : rowRead z (A.row j)=(A.mulVec z) j := by
    rw [row_read_value]
    rfl
  constructor
  · intro h i
    rw [hEval,h]
    rfl
  · intro h
    have hK : Submodule.span F₂ (Set.range fun i=>A.row (e i)) ≤ LinearMap.ker (rowRead z) :=
      Submodule.span_le.mpr (fun _ ⟨i,hi⟩=>LinearMap.mem_ker.mpr (hi ▸ h i))
    rw [hSp] at hK
    funext i
    rw [←hEval]
    exact LinearMap.mem_ker.mp (hK (Submodule.subset_span ⟨i,rfl⟩))

section Query
variable {V : Type*} [Fintype V] [DecidableEq V]

def violations (q : C→Quad V) (x : Finset V) : C→F₂ := fun i=>(q i).eval x

omit [Fintype R] [Fintype V] in
noncomputable def parityRow (A : Matrix R C F₂) (q : C→Quad V) (i : R) : Quad V :=
  combine q (A.row i)

omit [Fintype R] [Fintype V] in
theorem parity_row_exact (A : Matrix R C F₂) (q : C→Quad V) (i : R) (x : Finset V) :
    (parityRow A q i).eval x=(A.mulVec (violations q x)) i := by
  rw [parityRow,eval_combine]
  rfl

omit [Fintype R] in
noncomputable def hashedCount (A : Matrix R C F₂) (q : C→Quad V) : ℕ :=
  (Finset.univ.filter fun x : Finset V=> A.mulVec (violations q x)=0).card

theorem row_basis_preserves_count (A : Matrix R C F₂) (q : C→Quad V)
    (e : Fin A.rank ↪ R)
    (hSp : Submodule.span F₂ (Set.range fun i=>A.row (e i))=
      Submodule.span F₂ (Set.range A.row)) :
    hashedCount A q=zeroCount (fun i=>parityRow A q (e i)) := by
  classical
  unfold hashedCount zeroCount
  apply congrArg Finset.card
  ext x
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,parity_row_exact]
  rw [original_rows_equivalent A e hSp]
  apply forall_congr'
  intro i
  rw [row_read_value]
  rfl

theorem quadratic_hash_rank_divisible (A : Matrix R C F₂) (q : C→Quad V)
    (N : ℕ) (hV : Fintype.card V=2*N) :
    (2:ℕ)^(N-A.rank) ∣ hashedCount A q := by
  obtain ⟨e,_,hSp⟩ := exists_indexed_row_basis A
  rw [row_basis_preserves_count A q e hSp]
  simpa only [Fintype.card_fin] using zero_count_divisible N hV (fun i=>parityRow A q (e i))

theorem early_hash_even (A : Matrix R C F₂) (q : C→Quad V) (N : ℕ)
    (hV : Fintype.card V=2*N) (hA : A.rank<N) :
    2∣hashedCount A q := by
  have hd : (2:ℕ)^1 ∣ 2^(N-A.rank) := pow_dvd_pow _ (by omega)
  simpa only [pow_one] using hd.trans (quadratic_hash_rank_divisible A q N hV)

theorem odd_hash_rank_at_least (A : Matrix R C F₂) (q : C→Quad V) (N : ℕ)
    (hV : Fintype.card V=2*N) (hOdd : ¬2∣hashedCount A q) :
    N≤A.rank := by
  by_contra! h
  exact hOdd (early_hash_even A q N hV h)

omit [Fintype R] in
theorem one_count_requires_appends {a j : ℕ} (A : Matrix (Fin (a+j)) C F₂)
    (q : C→Quad V) (N : ℕ) (hV : Fintype.card V=2*N)
    (hCount : hashedCount A q=1) :
    N-a≤j := by
  have h := odd_hash_rank_at_least A q N hV (by rw [hCount]; decide)
  have hr := Matrix.rank_le_card_height A
  rw [Fintype.card_fin] at hr
  omega

end Query

#print axioms exists_indexed_row_basis
#print axioms row_read_value
#print axioms original_rows_equivalent
#print axioms parity_row_exact
#print axioms row_basis_preserves_count
#print axioms quadratic_hash_rank_divisible
#print axioms early_hash_even
#print axioms odd_hash_rank_at_least
#print axioms one_count_requires_appends
end Paper5.FrontendG1