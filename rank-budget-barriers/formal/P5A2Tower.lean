import P5A2Double

/-! A certified monomial basis extends by one actual polynomial quotient
over its current coefficient algebra. Iterating this construction from the
ground field gives the same exact rank for any finite number of variables. -/
namespace P5A2
open Polynomial Matrix Module
open scoped Classical BigOperators

variable {K A I : Type*} [Field K] [CommRing A] [Algebra K A] [Fintype I]

structure Chart (d : I → ℕ) where
  basis : Basis (Box d) K A
  mul_basis : ∀ u v : Box d,
    basis u * basis v =
      if h : ∀ i, (u i).val+(v i).val<d i then
        basis (fun i => ⟨(u i).val+(v i).val,h i⟩) else 0

theorem chart_coefficient_entry {d : I → ℕ} (C : Chart (K:=K) (A:=A) d)
    (a u v : Box d) :
    pairing C.basis (C.basis.coord a) u v =
      coordinateMatrix (K:=K) a u v := by
  unfold pairing coordinateMatrix
  simp only [Matrix.of_apply]
  rw [C.mul_basis]
  by_cases he : ∀ i, (u i).val+(v i).val=(a i).val
  · have hl : ∀ i, (u i).val+(v i).val<d i := fun i => he i ▸ (a i).isLt
    rw [dif_pos hl,if_pos he,coord_basis]
    exact if_pos (funext fun i => Fin.ext (he i))
  · rw [if_neg he]
    split
    · rename_i hl
      rw [coord_basis]
      rw [if_neg (fun h => he (fun i => congrArg (fun x : Box d => (x i).val) h))]
    · exact map_zero _

theorem chart_coefficient_rank {d : I → ℕ} (C : Chart (K:=K) (A:=A) d)
    (a : Box d) :
    (pairing C.basis (C.basis.coord a)).rank = ∏ i, ((a i).val+1) := by
  have h : pairing C.basis (C.basis.coord a) = coordinateMatrix (K:=K) a :=
    Matrix.ext (chart_coefficient_entry C a)
  rw [h]
  exact coordinateMatrix_rank (K:=K) a

omit [Fintype I] in
def appendCaps (d : I → ℕ) (k : ℕ) : Option I → ℕ
  | none => k
  | some i => d i

omit [Fintype I] in
def appendEquiv (d : I → ℕ) (k : ℕ) : Box (appendCaps d k) ≃ (Box d × Fin k) where
  toFun u := (fun i => u (some i),u none)
  invFun u i := match i with
    | none => u.2
    | some i => u.1 i
  left_inv u := funext fun i => by cases i <;> rfl
  right_inv u := rfl

set_option maxHeartbeats 5400000 in
/-- Extend the genuine algebra, not just an abstract matrix formula, by
one nilpotent variable of the selected truncation length. -/
noncomputable def appendChart [Nontrivial A] {d : I → ℕ}
    (C : Chart (K:=K) (A:=A) d) (k : ℕ) :
    Chart (K:=K) (A:=Trunc A k) (appendCaps d k) := by
  let e := appendEquiv d k
  let b := (C.basis.smulTower (powers A k)).reindex e.symm
  have hb (u : Box (appendCaps d k)) :
      b u = (algebraMap A (Trunc A k)) (C.basis (fun i => u (some i))) *
        powers A k (u none) := by
    simp [b,Basis.reindex_apply,Basis.smulTower_apply,Algebra.smul_def,e,appendEquiv]
  refine ⟨b,?_⟩
  intro u v
  rw [hb u,hb v,mul_mul_mul_comm,←map_mul,C.mul_basis,powers_mul]
  have hf :
      (∀ i, (u i).val+(v i).val<appendCaps d k i) ↔
        (∀ i, (u (some i)).val+(v (some i)).val<d i) ∧
          (u none).val+(v none).val<k := by
    constructor
    · intro h
      exact ⟨fun i => h (some i),h none⟩
    · intro h i
      cases i with
      | none => exact h.2
      | some i => exact h.1 i
  by_cases hl : ∀ i, (u (some i)).val+(v (some i)).val<d i
  · by_cases hr : (u none).val+(v none).val<k
    · rw [dif_pos hl,dif_pos hr,dif_pos (hf.mpr ⟨hl,hr⟩),hb]
    · rw [dif_pos hl,dif_neg hr,dif_neg (fun h => hr (hf.mp h).2),mul_zero]
  · rw [dif_neg hl,dif_neg (fun h => hl (hf.mp h).1),map_zero,zero_mul]

/-- Base case: the empty monomial box contains exactly the scalar unit. -/
noncomputable def emptyChart : Chart (K:=K) (A:=K) (I:=Empty) (fun i => Empty.elim i) := by
  let d : Empty → ℕ := fun i => Empty.elim i
  let z : Box d := fun i => Empty.elim i
  letI : Unique (Box d) := { default := z, uniq := fun u => funext fun i => Empty.elim i }
  let b := Basis.singleton (Box d) K
  refine ⟨b,?_⟩
  intro u v
  have hd : ∀ i, (u i).val+(v i).val<d i := fun i => Empty.elim i
  rw [dif_pos hd]
  have h (w : Box d) : b w = (1:K) := Basis.singleton_apply (Box d) K w
  change b u * b v = b (fun i => ⟨(u i).val+(v i).val,hd i⟩)
  rw [h u,h v,h,mul_one]

#print axioms chart_coefficient_entry
#print axioms chart_coefficient_rank
#print axioms appendChart
#print axioms emptyChart
end P5A2
