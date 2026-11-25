import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega

/-! The binary zero-degree converse for the centralized paired recovery model. -/

open scoped BigOperators Polynomial

namespace Reconstruction.TernaryCode

noncomputable section

/-- At each slot the first letter indexes the file and the second indexes the function. -/
abbrev Word (q : ℕ) := Fin q → Bool × Bool

/-- The kernel criterion for recovering all demands using the shared matrix and the
input slice specified by the output's second letter at the queried slot. -/
def Recovers {q : ℕ} {I : Type*} [Fintype I] (M : Matrix I (Word q) ℚ) : Prop :=
  ∀ (u : Word q) (t : Fin q) (z : Word q → ℚ),
    (∀ i, ∑ v, M i v * z v = 0) →
    (∀ v, (v t).1 = (u t).2 → z v = 0) → z u = 0

/-- The polynomial model at degree zero, with the physical side coordinates unchanged. -/
def FeasibleZero {q : ℕ} {I : Type*} [Fintype I] (a : Fin q → ℚ)
    (M : Matrix I (Word q) ℚ) (P : Matrix (Word q) (Word q) ℚ[X]) : Prop :=
  (∀ u v, (P u v).natDegree ≤ 0) ∧
  (∀ u v, (P u v).eval 0 = if u = v then 1 else 0) ∧
  ∀ (u : Word q) (t : Fin q) (z : Word q → ℚ),
    (∀ i, ∑ v, M i v * z v = 0) →
    (∀ v, (v t).1 = (u t).2 → z v = 0) →
    ∑ v, (P u v).eval (a t) * z v = 0

theorem feasibleZero_recovers {q : ℕ} {I : Type*} [Fintype I] {a : Fin q → ℚ}
    {M : Matrix I (Word q) ℚ} {P : Matrix (Word q) (Word q) ℚ[X]}
    (h : FeasibleZero a M P) : Recovers M := by
  classical
  intro u t z hz hs
  have eval (v : Word q) : (P u v).eval (a t) = if u = v then 1 else 0 := by
    have hconst := Polynomial.eq_C_of_natDegree_le_zero (h.1 u v)
    have ha := congrArg (fun p : ℚ[X] => p.eval (a t)) hconst
    have h0 := congrArg (fun p : ℚ[X] => p.eval 0) hconst
    simp only [Polynomial.eval_C] at ha h0
    exact ha.trans (h0.symm.trans (h.2.1 u v))
  simpa only [eval, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true] using h.2.2 u t z hz hs

theorem feasibleZero_exists_iff {q : ℕ} {I : Type*} [Fintype I]
    (a : Fin q → ℚ) (M : Matrix I (Word q) ℚ) :
    (∃ P, FeasibleZero a M P) ↔ Recovers M := by
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

private def selected : (q : ℕ) → Word q → Prop
  | 0, _ => False
  | q + 1, w => w 0 = (true, false) ∨ w 0 = (true, true) ∧ selected q (Fin.tail w)

private abbrev Selected (q : ℕ) := {w : Word q // selected q w}

private noncomputable instance (q : ℕ) : Fintype (Selected q) := Fintype.ofFinite _

private def selectedSucc (q : ℕ) : Word q ⊕ Selected q ≃ Selected (q + 1) where
  toFun := Sum.elim
    (fun w => ⟨Fin.cons (true, false) w, Or.inl (Fin.cons_zero _ _)⟩)
    (fun w => ⟨Fin.cons (true, true) w.1, Or.inr ⟨Fin.cons_zero _ _,
      by simpa only [Fin.tail_cons] using w.2⟩⟩)
  invFun w := if h : w.val 0 = (true, false) then Sum.inl (Fin.tail w.val)
    else Sum.inr ⟨Fin.tail w.val, (w.property.resolve_left h).2⟩
  left_inv w := by
    cases w with
    | inl w => simp
    | inr w => simp
  right_inv w := by
    dsimp
    split_ifs with hw
    · apply Subtype.ext
      change Fin.cons (true, false) (Fin.tail w.val) = w.val
      rw [← hw, Fin.cons_self_tail]
    · apply Subtype.ext
      change Fin.cons (true, true) (Fin.tail w.val) = w.val
      rw [← (w.property.resolve_left hw).1, Fin.cons_self_tail]

private theorem word_card (q : ℕ) : Fintype.card (Word q) = 4 ^ q := by
  simp [Fintype.card_prod]

/-- The recurrence for the finite binary receiver-order count. -/
theorem binary_count_succ (q : ℕ) :
    (4 ^ (q + 1) - 1) / 3 = 4 ^ q + (4 ^ q - 1) / 3 := by
  have hpow : 0 < 4 ^ q := pow_pos (by decide) _
  rw [pow_succ]
  omega

private theorem selected_card (q : ℕ) :
    Fintype.card (Selected q) = (4 ^ q - 1) / 3 := by
  classical
  induction q with
  | zero =>
      letI : IsEmpty (Selected 0) := ⟨fun v => v.property⟩
      simp
  | succ q ih =>
      rw [← Fintype.card_congr (selectedSucc q), Fintype.card_sum, word_card, ih,
        binary_count_succ]

/-- If a difference is supported on the selected receiver-order columns, the receivers
eliminate the first block and then repeat on the surviving tail. -/
private theorem selected_zero (q : ℕ) (z : Word q → ℚ)
    (hs : ∀ v, ¬ selected q v → z v = 0)
    (hr : ∀ (u : Word q) (t : Fin q),
      (∀ v, (v t).1 = (u t).2 → z v = 0) → z u = 0) :
    ∀ v, z v = 0 := by
  induction q with
  | zero => exact fun v => hs v id
  | succ q ih =>
      have skip (v : Word (q + 1)) (hv : v 0 ≠ (true, true)) : z v = 0 := by
        by_cases h : v 0 = (true, false)
        · apply hr v 0
          intro w hw
          apply hs
          intro hsel
          have hfirst : (w 0).1 = true := hsel.elim (fun e => congrArg Prod.fst e)
            (fun e => congrArg Prod.fst e.1)
          simp [h, hfirst] at hw
        · exact hs v (fun hsel => hsel.elim h (fun e => hv e.1))
      let tailInput (v : Word q) := z (Fin.cons (true, true) v)
      have htail := ih tailInput (fun v hv => by
        apply hs
        simpa [selected] using hv) (fun u t hside => by
        apply hr (Fin.cons (true, true) u) t.succ
        intro v hv
        by_cases hhead : v 0 = (true, true)
        · have he : Fin.cons (true, true) (Fin.tail v) = v := by
            rw [← hhead, Fin.cons_self_tail]
          have h := hside (Fin.tail v) (by simpa using hv)
          simpa only [tailInput, he] using h
        · exact skip v hhead)
      intro v
      by_cases hv : v 0 = (true, true)
      · have he : Fin.cons (true, true) (Fin.tail v) = v := by
          rw [← hv, Fin.cons_self_tail]
        simpa only [tailInput, he] using htail (Fin.tail v)
      · exact skip v hv

/-- The sharp central converse, in terms of matrix rank and arbitrary rational rows. -/
theorem rank_lower_of_recovers {q : ℕ} {I : Type*} [Fintype I]
    (M : Matrix I (Word q) ℚ) (hm : Recovers M) :
    (4 ^ q - 1) / 3 ≤ M.rank := by
  classical
  let A : Matrix I (Selected q) ℚ := M.submatrix id Subtype.val
  have hinj : Function.Injective A.mulVecLin := LinearMap.ker_eq_bot.mp (by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    let z (v : Word q) : ℚ := if h : selected q v then x ⟨v, h⟩ else 0
    have hz (i : I) : ∑ v, M i v * z v = 0 := by
      have h := congrFun hx i
      change (∑ v : Selected q, M i v.val * x v) = 0 at h
      rw [← h]
      calc
        _ = ∑ v ∈ Finset.univ.filter (selected q), M i v * z v := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro v _
          by_cases hv : selected q v <;> simp [z, hv]
        _ = ∑ v : Selected q, M i v.val * z v.val :=
          Finset.sum_subtype _ (by simp) _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro v _
          simp [z, v.property]
    have hzero := selected_zero q z (fun v hv => dif_neg hv)
      (fun u t hside => hm u t z hz hside)
    funext v
    simpa [z, v.property] using hzero v.val)
  have ha : A.rank = Fintype.card (Selected q) := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hinj, Module.finrank_pi]
  rw [← selected_card, ← ha]
  have ht : A.transpose.rank ≤ M.transpose.rank :=
    Matrix.rank_submatrix_le Subtype.val (Equiv.refl I) M.transpose
  simpa only [Matrix.rank_transpose] using ht

theorem rank_lower_of_feasibleZero {q : ℕ} {I : Type*} [Fintype I]
    {a : Fin q → ℚ} {M : Matrix I (Word q) ℚ} {P : Matrix (Word q) (Word q) ℚ[X]}
    (h : FeasibleZero a M P) : (4 ^ q - 1) / 3 ≤ M.rank :=
  rank_lower_of_recovers M (feasibleZero_recovers h)

end
end Reconstruction.TernaryCode
