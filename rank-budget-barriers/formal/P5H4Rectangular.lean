import P5H4IrredTransport

/-! Extract a genuine rectangular quotient-image chart from the PID
submodule of columns. The rectangular chart uses a polynomial row basis
and mutually generated columns; no nonzero determinant of A is assumed. -/
namespace P5H4
open Polynomial Matrix Module
open scoped Classical BigOperators

variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]

/-- A rectangular diagonal uses actual distinct rows for the retained
diagonals. All other entries are zero. -/
noncomputable def rowDiagonal {r : Type*} (e : r ↪ m) (a : r → K[X]) : Matrix m r K[X] :=
  Matrix.of fun i j => if i = e j then a j else 0

set_option maxHeartbeats 3400000 in
theorem rowDiagonal_image {r : Type*} [Fintype r] [DecidableEq r] (e : r ↪ m)
    (a : r → K[X]) (q : K[X]) (hq : q.Monic) :
    quotientLength (rowDiagonal e a) q = quotientLength (diagonal a) q := by
  let J : Matrix m r K[X] := rowDiagonal e (fun _ => 1)
  let S : Matrix r m K[X] := Jᵀ
  have hJ : J * diagonal a = rowDiagonal e a := by
    apply Matrix.ext
    intro i j
    rw [Matrix.mul_diagonal]
    simp [J,rowDiagonal,apply_ite (fun y : K[X] => y*a j)]
  have hSJ : S * J = 1 := by
    apply Matrix.ext
    intro i j
    rw [Matrix.mul_apply,Finset.sum_eq_single (e j)]
    · by_cases hj : i=j
      · subst j
        simp [S,J,rowDiagonal]
      · have hn : (e j : m) ≠ e i := fun he => hj (e.injective he.symm)
        simp [S,J,rowDiagonal,hn,Matrix.one_apply_ne hj]
    · intro k _ hk
      simp [S,J,rowDiagonal,hk]
    · simp
  have hS : S * rowDiagonal e a = diagonal a := by
    rw [← hJ,←Matrix.mul_assoc,hSJ,Matrix.one_mul]
  exact le_antisymm (hJ ▸ (quotientLength_mul_le J (diagonal a) q hq).2)
    (hS ▸ (quotientLength_mul_le S (rowDiagonal e a) q hq).2)

set_option maxHeartbeats 6000000 in
/-- Global polynomial chart for every rectangular matrix, including zero
and singular square matrices. Return actual mutually spanning columns. -/
theorem rectangular_chart (A : Matrix m n K[X]) :
    ∃ (r : ℕ) (e : Fin r ↪ m) (a : Fin r → K[X]) (U : Matrix m m K[X])
      (Z : Matrix m (Fin r) K[X]) (C : Matrix (Fin r) n K[X])
      (T : Matrix n (Fin r) K[X]),
      (∀ i, a i ≠ 0) ∧ IsUnit U ∧ U*Z = rowDiagonal e a ∧ Z*C = A ∧ A*T = Z := by
  let b := Pi.basisFun K[X] m
  let F := A.mulVecLin
  let N := LinearMap.range F
  obtain ⟨r,S⟩ := N.smithNormalForm b
  let V : Fin r → m → K[X] := fun j => (S.bN j).val
  let Z : Matrix m (Fin r) K[X] := b.toMatrix V
  let U : Matrix m m K[X] := S.bM.toMatrix b
  have hz (i : m) (j : Fin r) : Z i j = (S.bN j).val i := by
    simp only [Z,V,b,Module.Basis.toMatrix_apply,Pi.basisFun_repr]
  have hb (B₁ B₂ : Basis m K[X] (m→K[X])) : B₁.toMatrix B₂ * B₂.toMatrix B₁=1 := by
    rw [Basis.toMatrix_mul_toMatrix, Basis.toMatrix_self]
  have hu : IsUnit U := ⟨⟨U,b.toMatrix S.bM,hb _ _,hb _ _⟩,rfl⟩
  have ha (i : Fin r) : S.a i ≠ 0 := by
    intro hi
    apply S.bN.ne_zero i
    apply Subtype.ext
    simpa [hi] using S.snf i
  have hU : U*Z = rowDiagonal S.f S.a := by
    change (S.bM.toMatrix b) * (b.toMatrix V) = _
    rw [Basis.toMatrix_mul_toMatrix]
    apply Matrix.ext
    intro i j
    rw [Basis.toMatrix_apply]
    change S.bM.repr ((S.bN j).val) i = if i = S.f j then S.a j else 0
    rw [S.snf, LinearEquiv.map_smul, Finsupp.smul_apply,Basis.repr_self, Finsupp.single_apply]
    by_cases h : i = S.f j
    · subst i
      simp
    · simp [h,Ne.symm h]
  have he (j : n) : (fun i => A i j) ∈ N := by
    refine ⟨Pi.single j 1,?_⟩
    change A *ᵥ Pi.single j 1 = _
    funext i
    simp [Matrix.mulVec_single]
  let J (j : n) : N := ⟨fun i => A i j, he j⟩
  let C : Matrix (Fin r) n K[X] := Matrix.of fun i j => S.bN.repr (J j) i
  have hC : Z*C = A := by
    apply Matrix.ext
    intro i j
    have h := congrArg (fun (v : N) => v.val i) (S.bN.sum_repr (J j))
    change (∑ k, Z i k * S.bN.repr (J j) k) = A i j
    simpa only [hz,Submodule.coe_sum,Submodule.coe_smul,Finset.sum_apply,Pi.smul_apply,
      smul_eq_mul,mul_comm] using h
  have hh (j : Fin r) : ∃ w : n→K[X], A *ᵥ w = (S.bN j).val := (S.bN j).property
  choose w hw using hh
  let T : Matrix n (Fin r) K[X] := Matrix.of fun i j => w j i
  have hT : A*T = Z := by
    apply Matrix.ext
    intro i j
    rw [hz]
    exact congrFun (hw j) i
  exact ⟨r,S.f,S.a,U,Z,C,T,ha,hu,hU,hC,hT⟩

set_option maxHeartbeats 5000000 in
/-- Exact quotient rank profile of the same rectangular matrix at all
irreducibles and all truncations, without regularity of the matrix. -/
theorem rectangular_quotient_profile (A : Matrix m n K[X]) :
    ∃ (r : ℕ) (a : Fin r → K[X]), (∀ i, a i ≠ 0) ∧
      ∀ (f : K[X]), f.Monic → Irreducible f → ∀ k,
        quotientLength A (f^k) = ∑ i, f.natDegree*(k-min k (multiplicity f (a i))) := by
  obtain ⟨r,e,a,U,Z,C,T,ha,hU,hu,hC,hT⟩ := rectangular_chart A
  refine ⟨r,a,ha,fun f hm hf k => ?_⟩
  have hq : (f^k).Monic := hm.pow k
  have hAZ : quotientLength A (f^k) = quotientLength Z (f^k) := by
    refine le_antisymm ?_ ?_
    · rw [← hC]
      exact (quotientLength_mul_le Z C _ hq).1
    · rw [← hT]
      exact (quotientLength_mul_le A T _ hq).1
  have hUZ := (quotientLength_unimodular Z U (1:Matrix (Fin r) (Fin r) K[X])
    hU isUnit_one (f^k) hq)
  rw [Matrix.mul_one,hu] at hUZ
  rw [hAZ,←hUZ,rowDiagonal_image e a _ hq,irreducible_diagonal_length f hm hf a ha k]

#print axioms rowDiagonal_image
#print axioms rectangular_chart
#print axioms rectangular_quotient_profile
end P5H4
