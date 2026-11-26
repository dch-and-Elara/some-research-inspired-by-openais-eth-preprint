import P5FrontendG1Rank
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval

/-! Any honest degree-at-most-two F2 polynomial fits the list
support representation on the Boolean cube, including squared
variables and constants. This closes the paper's abstract polynomial
quantifier in addition to the literal guarded clause instance. -/
namespace Paper5.FrontendG1
open scoped BigOperators
open MvPolynomial

variable {V : Type*} [DecidableEq V]

def cubePoint (x : Finset V) : V→F₂ := fun i=>if i∈x then 1 else 0

omit [DecidableEq V] in
theorem card_exponent_support_le (d : V→₀ℕ) :
    d.support.card≤∑ i ∈ d.support,d i := by
  calc
    _ = ∑ _i ∈ d.support,(1:ℕ) := by simp
    _ ≤ _ := Finset.sum_le_sum
      (fun i hi=>Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))

noncomputable def compileQuad (p : MvPolynomial V F₂) (hp : p.totalDegree≤2) : Quad V :=
  ⟨p.support.toList.map Finsupp.support, fun t ht=>by
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp ht
    exact (card_exponent_support_le d).trans ((le_totalDegree (Finset.mem_toList.mp hd)).trans hp)⟩

theorem monomial_evaluation_exact (d : V→₀ℕ) (x : Finset V) :
    (∏ i ∈ d.support,(cubePoint x i)^(d i)) = mon d.support x := by
  unfold mon
  by_cases h : d.support⊆x
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro i hi
    simp [cubePoint,h hi]
  · rw [if_neg h]
    obtain ⟨i,hi,hn⟩ := Finset.not_subset.mp h
    exact Finset.prod_eq_zero hi (by
      simp [cubePoint,hn,zero_pow (Finsupp.mem_support_iff.mp hi)])

theorem compile_quad_exact (p : MvPolynomial V F₂) (hp : p.totalDegree≤2) (x : Finset V) :
    (compileQuad p hp).eval x = MvPolynomial.eval (cubePoint x) p := by
  unfold Quad.eval compileQuad
  rw [List.map_map,Finset.sum_map_toList,MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro d hd
  rw [monomial_evaluation_exact]
  have hc : p.coeff d=1 := (binary_cases (p.coeff d)).resolve_left
    (MvPolynomial.mem_support_iff.mp hd)
  rw [hc,one_mul]
  rfl

noncomputable def polynomialHashedCount {C R : Type*} [Fintype V] [Fintype C]
    (A : Matrix R C F₂) (p : C→MvPolynomial V F₂) : ℕ := by
  classical
  exact (Finset.univ.filter fun x : Finset V=> A.mulVec (fun c=>MvPolynomial.eval (cubePoint x) (p c))=0).card

theorem polynomial_hash_rank_divisible {C R : Type*} [Fintype V] [Fintype C] [Fintype R]
    (A : Matrix R C F₂) (p : C→MvPolynomial V F₂) (hp : ∀ c,(p c).totalDegree≤2)
    (N : ℕ) (hV : Fintype.card V=2*N) :
    (2:ℕ)^(N-A.rank) ∣ polynomialHashedCount A p := by
  let q := fun c=>compileQuad (p c) (hp c)
  have he : polynomialHashedCount A p=hashedCount A q := by
    classical
    unfold polynomialHashedCount hashedCount
    apply congrArg Finset.card
    ext x
    have hv : violations q x=(fun c=>MvPolynomial.eval (cubePoint x) (p c)) := by
      funext c
      exact compile_quad_exact (p c) (hp c) x
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    rw [hv]
  rw [he]
  exact quadratic_hash_rank_divisible A q N hV

#print axioms card_exponent_support_le
#print axioms monomial_evaluation_exact
#print axioms compile_quad_exact
#print axioms polynomial_hash_rank_divisible
end Paper5.FrontendG1