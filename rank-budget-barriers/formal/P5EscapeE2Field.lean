import P5EscapeE2Canonical
import Mathlib.FieldTheory.Finite.GaloisField

/-! Nonlinear growth from one cached rank-two field difference. The power
routine has a fixed arithmetic trace and counts actual field
multiplications, not the monomial count after expansion. -/
namespace Paper5.EscapeE2
open scoped BigOperators

def mersenneRun {K : Type*} [Monoid K] (s : K) : ℕ→K×ℕ
  | 0 => (1,0)
  | j+1 =>
    let t := mersenneRun s j
    (t.1*t.1*s,t.2+2)

theorem mersenne_run_eval {K : Type*} [Monoid K] (s : K) (m : ℕ) :
    mersenneRun s m=(s^(2^m-1),2*m) := by
  induction m with
  | zero => simp [mersenneRun]
  | succ j ih =>
    simp only [mersenneRun,ih]
    congr 1
    · rw [←pow_add,←pow_succ]
      congr 1
      have h : (0:ℕ)<2^j := by positivity
      rw [pow_succ]
      omega

/-- One cached subtraction supplies the seed to every iteration. -/
def cachedRun {K : Type*} [Field K] (m : ℕ) (x y : K) : K×ℕ :=
  let s := x-y
  let p := mersenneRun s m
  (1-p.1,p.2+2)

theorem cached_run_cost {K : Type*} [Field K] (m : ℕ) (x y : K) :
    (cachedRun m x y).2=2*m+2 := by
  rw [cachedRun,mersenne_run_eval]

theorem cached_run_indicator {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (m : ℕ) (hm : 0<m) (hK : Fintype.card K=2^m) (x y : K) :
    (cachedRun m x y).1=(if x=y then 1 else 0) := by
  rw [cachedRun,mersenne_run_eval]
  by_cases H : x=y
  · have hPow : 1<(2:ℕ)^m := Nat.one_lt_pow (by omega) (by decide)
    have hsub : 2^m-1≠0 := by omega
    simp [H,hsub]
  · have h := FiniteField.pow_card_sub_one_eq_one (x-y) (sub_ne_zero.mpr H)
    rw [hK] at h
    simp [H,h]

def cachedMatrix (K : Type*) [Field K] (m : ℕ) : Matrix K K K :=
  Matrix.of fun x y=>(cachedRun m x y).1

theorem cached_matrix_eq_one {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (m : ℕ) (hm : 0<m) (hK : Fintype.card K=2^m) :
    cachedMatrix K m=1 := by
  ext x y
  rw [cachedMatrix,Matrix.of_apply,cached_run_indicator m hm hK,Matrix.one_apply]

theorem cached_field_rank_amplification {K : Type*} [Field K] [Fintype K]
    (m : ℕ) (hm : 0<m) (hK : Fintype.card K=2^m) :
    (difference (id : K→K) id).rank≤2 ∧ (cachedMatrix K m).rank=2^m ∧
      ∀ x y : K,(cachedRun m x y).2=2*m+2 := by
  classical
  refine ⟨difference_rank_le_two _ _,?_,cached_run_cost m⟩
  rw [cached_matrix_eq_one m hm hK,Matrix.rank_one,hK]

noncomputable def fieldBitEncoding {K : Type*} [Field K] [Fintype K]
    (m : ℕ) (hK : Fintype.card K=2^m) : (Fin m→Bool) ≃ K :=
  Fintype.equivOfCardEq (by simp [hK])

theorem binary_field_meters (m : ℕ) (hm : 0<m) :
    ∃ (K : Type) (_ : Field K) (t : Fintype K), @Fintype.card K t=2^m := by
  let K := GaloisField 2 m
  letI : Fintype K := Fintype.ofFinite K
  refine ⟨K,inferInstance,inferInstance,?_⟩
  rw [←Nat.card_eq_fintype_card]
  exact GaloisField.card 2 m hm.ne'

#print axioms mersenne_run_eval
#print axioms cached_run_cost
#print axioms cached_run_indicator
#print axioms cached_matrix_eq_one
#print axioms cached_field_rank_amplification
#print axioms fieldBitEncoding
#print axioms binary_field_meters
end Paper5.EscapeE2