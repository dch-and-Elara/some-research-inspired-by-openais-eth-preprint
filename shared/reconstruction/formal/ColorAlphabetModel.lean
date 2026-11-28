import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fintype.BigOperators

open scoped BigOperators Polynomial

namespace Reconstruction.ColorAlphabet

noncomputable section

/-- An input column is a file/function pair at each position. -/
abbrev Word {T : Type*} (A : T → Type*) := ∀ t, A t × A t

abbrev Receiver {T : Type*} (A : T → Type*) := Sigma A

def Holds {T : Type*} {A : T → Type*} (x : Receiver A) (v : Word A) : Prop :=
  (v x.1).1 = x.2

def Demands {T : Type*} {A : T → Type*} (x : Receiver A) (v : Word A) : Prop :=
  (v x.1).2 = x.2

variable {T F I : Type*} {A : T → Type*}
  [Fintype T] [DecidableEq T] [∀ t, Fintype (A t)] [∀ t, DecidableEq (A t)]
  [Field F] [Fintype I]

/-- The common measurements determine each demand given the receiver's side coordinates. -/
def Recovers (C : Matrix I (Word A) F) : Prop :=
  ∀ (u : Word A) (t : T) (z : Word A → F),
    (∀ i, ∑ v, C i v * z v = 0) →
    (∀ v, (v t).1 = (u t).2 → z v = 0) → z u = 0

/-- The degree-zero specialization of the polynomial model. -/
def FeasibleZero (a : T → F) (C : Matrix I (Word A) F)
    (P : Matrix (Word A) (Word A) F[X]) : Prop :=
  (∀ u v, (P u v).natDegree ≤ 0) ∧
  (∀ u v, (P u v).eval 0 = if u = v then 1 else 0) ∧
  ∀ (u : Word A) (t : T) (z : Word A → F),
    (∀ i, ∑ v, C i v * z v = 0) →
    (∀ v, (v t).1 = (u t).2 → z v = 0) →
    ∑ v, (P u v).eval (a t) * z v = 0

omit [Fintype I] in
theorem feasibleZero_recovers {a : T → F} {C : Matrix I (Word A) F}
    {P : Matrix (Word A) (Word A) F[X]} (h : FeasibleZero a C P) : Recovers C := by
  classical
  intro u t z hz hs
  have eval (v : Word A) : (P u v).eval (a t) = if u = v then 1 else 0 := by
    have hc := Polynomial.eq_C_of_natDegree_le_zero (h.1 u v)
    have ha := congrArg (fun p : F[X] => p.eval (a t)) hc
    have h0 := congrArg (fun p : F[X] => p.eval 0) hc
    simp only [Polynomial.eval_C] at ha h0
    exact ha.trans (h0.symm.trans (h.2.1 u v))
  simpa only [eval, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true] using h.2.2 u t z hz hs

theorem feasibleZero_exists_iff (a : T → F) (C : Matrix I (Word A) F) :
    (∃ P, FeasibleZero a C P) ↔ Recovers C := by
  classical
  refine ⟨fun ⟨P, hP⟩ => feasibleZero_recovers hP, fun h => ?_⟩
  refine ⟨fun u v => Polynomial.C (if u = v then 1 else 0), ?_, ?_, ?_⟩
  · intro u v
    exact (Polynomial.natDegree_C _).le
  · intro u v
    exact Polynomial.eval_C
  · intro u t z hz hs
    simpa only [Polynomial.eval_C, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true] using h u t z hz hs

/-- Each nonempty subcollection admits a receiver demanding a member and holding none. -/
def GeneralizedIndependent (S : Finset (Word A)) : Prop :=
  ∀ U : Finset (Word A), U ⊆ S → U.Nonempty →
    ∃ x : Receiver A, (∃ u ∈ U, Demands x u) ∧ ∀ v ∈ U, ¬ Holds x v

theorem generalizedIndependent_rank_le (C : Matrix I (Word A) F) (hC : Recovers C)
    (S : Finset (Word A)) (hS : GeneralizedIndependent S) : S.card ≤ C.rank := by
  classical
  let M : Matrix I S F := C.submatrix id Subtype.val
  have hm : Function.Injective M.mulVecLin := LinearMap.ker_eq_bot.mp (by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    let z (v : Word A) : F := if hv : v ∈ S then c ⟨v, hv⟩ else 0
    have hz (i : I) : ∑ v, C i v * z v = 0 := by
      have h := congrFun hc i
      change (∑ v : S, C i v.val * c v) = 0 at h
      rw [← h]
      calc
        _ = ∑ v ∈ S, C i v * z v := by
          have hfilter : Finset.univ.filter (· ∈ S) = S := by ext v; simp
          rw [← hfilter, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro v _
          by_cases hv : v ∈ S <;> simp [z, hv]
        _ = ∑ v : S, C i v.val * z v.val := Finset.sum_subtype _ (by simp) _
        _ = _ := by simp [z, Subtype.property]
    by_contra hn
    let U := S.filter (fun v => z v ≠ 0)
    have hu : U.Nonempty := by
      by_contra! he
      apply hn
      funext v
      have hv : z v.val = 0 := by
        by_contra hn
        exact he ⟨v.val, Finset.mem_filter.mpr ⟨v.property, hn⟩⟩
      simpa [z, v.property] using hv
    obtain ⟨x, ⟨u, huU, hx⟩, hh⟩ := hS U (Finset.filter_subset _ _) hu
    have hside (v : Word A) (hv : (v x.1).1 = (u x.1).2) : z v = 0 := by
      by_contra hne
      have hvS : v ∈ S := by
        by_contra hv
        exact hne (dif_neg hv)
      exact hh v (Finset.mem_filter.mpr ⟨hvS, hne⟩) (hv.trans hx)
    exact (Finset.mem_filter.mp huU).2 (hC u x.1 z hz hside))
  have hr : M.rank = S.card := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hm, Module.finrank_pi, Fintype.card_coe]
  rw [← hr]
  have ht : M.transpose.rank ≤ C.transpose.rank :=
    Matrix.rank_submatrix_le Subtype.val (Equiv.refl I) C.transpose
  simpa only [Matrix.rank_transpose] using ht

end

end Reconstruction.ColorAlphabet
