import TernaryCodeLower
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! The rational three-color tensor encoder and the exact binary zero-degree rank. -/

open scoped BigOperators Polynomial

namespace Reconstruction.TernaryCode

private abbrev Row := Fin 4

private def color (k : Row) : ZMod 3 :=
  if k.val < 2 then 0 else if k.val = 2 then 1 else 2

private def entry (k : Row) (p : Bool × Bool) : ℚ :=
  match k.val with
  | 0 => if p.2 = false then 1 else 0
  | 1 => if p.2 = true then 1 else 0
  | 2 => if p.1 ≠ p.2 then 1 else 0
  | _ => if p = (false, true) then 1 else if p = (true, false) then -1 else 0

private def inverseEntry (p : Bool × Bool) (k : Row) : ℚ :=
  match p with
  | (false, false) => ![1, 0, -1/2, 1/2] k
  | (false, true) => ![0, 0, 1/2, 1/2] k
  | (true, false) => ![0, 0, 1/2, -1/2] k
  | (true, true) => ![0, 1, -1/2, -1/2] k

private theorem entry_ternary (k : Row) (p : Bool × Bool) :
    entry k p = -1 ∨ entry k p = 0 ∨ entry k p = 1 := by
  rcases p with ⟨a, b⟩
  fin_cases k <;> cases a <;> cases b <;> decide

private theorem local_expansion (u v : Bool × Bool) :
    (∑ k, inverseEntry u k * entry k v) = if u = v then 1 else 0 := by
  rcases u with ⟨a,b⟩
  rcases v with ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> rw [Fin.sum_univ_four] <;> decide +kernel

private def rowFor (g : ZMod 3) (receiver : Bool) : Row :=
  if g = 0 then (if receiver then 1 else 0) else if g = 1 then 2 else 3

private def signFor (g : ZMod 3) (receiver : Bool) : ℚ :=
  if g = 2 ∧ receiver = false then -1 else 1

private theorem color_rowFor (g : ZMod 3) (b : Bool) : color (rowFor g b) = g := by
  fin_cases g <;> cases b <;> decide

private theorem local_decode (g : ZMod 3) (u v : Bool × Bool)
    (hu : u.1 ≠ u.2) (hv : v.1 ≠ u.2) :
    signFor g u.2 * entry (rowFor g u.2) v = if u = v then 1 else 0 := by
  rcases u with ⟨a,b⟩
  rcases v with ⟨c,d⟩
  fin_cases g <;> cases a <;> cases b <;> cases c <;> cases d <;>
    first | exact (hu rfl).elim | exact (hv rfl).elim | decide +kernel

/-- Color of the tensor row, i.e. the sum of its one-site colors modulo three. -/
def totalColor {q : ℕ} (s : Fin q → Fin 4) : ZMod 3 := ∑ t, color (s t)

abbrev ColoredRows (q : ℕ) (g : ZMod 3) :=
  {s : Fin q → Fin 4 // totalColor s = g}

private theorem color_cons {q : ℕ} (k : Row) (s : Fin q → Row) :
    totalColor (Fin.cons k s) = color k + totalColor s := by
  simp [totalColor, Fin.sum_univ_succ]

private def coloredRowsSucc (q : ℕ) (g : ZMod 3) :
    (Σ k : Row, ColoredRows q (g - color k)) ≃ ColoredRows (q + 1) g where
  toFun p := ⟨Fin.cons p.1 p.2.val, by rw [color_cons, p.2.property, add_sub_cancel]⟩
  invFun s := ⟨s.val 0, ⟨Fin.tail s.val, by
    apply eq_sub_of_add_eq'
    rw [← color_cons, Fin.cons_self_tail]
    exact s.property⟩⟩
  left_inv := by
    rintro ⟨k, s⟩
    simp
  right_inv s := by
    apply Subtype.ext
    exact Fin.cons_self_tail _

private theorem color_offsets (g : ZMod 3) :
    (∑ k : Row, if g - color k = 0 then (1 : ℕ) else 0) =
      1 + if g = 0 then 1 else 0 := by
  fin_cases g <;> rw [Fin.sum_univ_four] <;> decide +kernel

private theorem three_times_count (q : ℕ) : 3 * ((4 ^ q - 1) / 3) + 1 = 4 ^ q := by
  induction q with
  | zero => decide
  | succ q ih =>
    rw [binary_count_succ, pow_succ]
    omega

/-- Exact count of tensor rows at each color. -/
theorem coloredRows_card (q : ℕ) (g : ZMod 3) :
    Fintype.card (ColoredRows q g) = (4 ^ q - 1) / 3 + if g = 0 then 1 else 0 := by
  classical
  induction q generalizing g with
  | zero =>
    by_cases hg : g = 0
    · subst g
      let e : ColoredRows 0 0 ≃ (Fin 0 → Row) :=
        { toFun := Subtype.val
          invFun := fun s => ⟨s, by simp [totalColor]⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Fintype.card_congr e]
      simp
    · letI : IsEmpty (ColoredRows 0 g) :=
        ⟨fun s => hg (s.property.symm.trans (by simp [totalColor]))⟩
      simp [hg]
  | succ q ih =>
    rw [← Fintype.card_congr (coloredRowsSucc q g), Fintype.card_sigma, binary_count_succ]
    simp only [ih, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, color_offsets]
    have hc := three_times_count q
    omega

/-- Transmit the product rows of total color one. -/
def encoder (q : ℕ) : Matrix (ColoredRows q 1) (Word q) ℚ :=
  fun s v => ∏ t, entry (s.val t) (v t)

theorem encoder_ternary (q : ℕ) (s : ColoredRows q 1) (v : Word q) :
    encoder q s v = -1 ∨ encoder q s v = 0 ∨ encoder q s v = 1 := by
  apply Finset.prod_induction _ (fun x : ℚ => x = -1 ∨ x = 0 ∨ x = 1)
  · intro a b ha hb
    rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> norm_num [ha, hb]
  · exact Or.inr (Or.inr rfl)
  · exact fun t _ => entry_ternary _ _

private def insertRow {q : ℕ} (t : Fin (q + 1)) (b : Bool)
    (s : Fin q → Row) : ColoredRows (q + 1) 1 :=
  ⟨t.insertNth (rowFor (1 - totalColor s) b) s, by
    rw [totalColor, Fin.sum_univ_succAbove _ t]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, color_rowFor]
    exact sub_add_cancel 1 (totalColor s)⟩

private def decoderCoeff {q : ℕ} (u : Word (q + 1)) (t : Fin (q + 1))
    (s : Fin q → Row) : ℚ :=
  signFor (1 - totalColor s) (u t).2 *
    ∏ i, inverseEntry (u (t.succAbove i)) (s i)

private theorem product_delta {q : ℕ} (u v : Word q) :
    (∏ i, if u i = v i then (1 : ℚ) else 0) = if u = v then 1 else 0 := by
  by_cases h : u = v
  · simp [h]
  · obtain ⟨i, hi⟩ : ∃ i, u i ≠ v i := by
      by_contra! he
      exact h (funext he)
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- On the unknown slice, a coordinate row is a combination of transmitted rows. -/
private theorem expand_on_unknown {q : ℕ} (u v : Word (q + 1)) (t : Fin (q + 1))
    (hu : (u t).1 ≠ (u t).2) (hv : (v t).1 ≠ (u t).2) :
    (∑ s : Fin q → Row, decoderCoeff u t s * encoder (q + 1) (insertRow t (u t).2 s) v) =
      if u = v then 1 else 0 := by
  have hterm (s : Fin q → Row) :
      decoderCoeff u t s * encoder (q + 1) (insertRow t (u t).2 s) v =
        (if u t = v t then 1 else 0) *
          ∏ i, inverseEntry (u (t.succAbove i)) (s i) *
            entry (s i) (v (t.succAbove i)) := by
    rw [decoderCoeff, encoder, Fin.prod_univ_succAbove _ t]
    simp only [insertRow, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
    rw [mul_mul_mul_comm, local_decode _ _ _ hu hv, Finset.prod_mul_distrib]
  simp only [hterm, ← Finset.mul_sum]
  rw [← Fintype.prod_sum (fun (i : Fin q) (k : Row) =>
    inverseEntry (u (t.succAbove i)) k * entry k (v (t.succAbove i)))]
  simp only [local_expansion]
  rw [← Fin.prod_univ_succAbove (fun i => if u i = v i then (1 : ℚ) else 0) t, product_delta]

theorem encoder_recovers (q : ℕ) : Recovers (encoder q) := by
  classical
  intro u t z hz hs
  cases q with
  | zero => exact Fin.elim0 t
  | succ q =>
    by_cases hu : (u t).1 = (u t).2
    · exact hs u hu
    · calc
        z u = ∑ v, (if u = v then 1 else 0) * z v := by simp [ite_mul]
        _ = ∑ v, (∑ s : Fin q → Row,
              decoderCoeff u t s * encoder (q + 1) (insertRow t (u t).2 s) v) * z v := by
          apply Finset.sum_congr rfl
          intro v _
          by_cases hv : (v t).1 = (u t).2
          · simp [hs v hv]
          · rw [expand_on_unknown u v t hu hv]
        _ = 0 := by
          simp only [Finset.sum_mul, mul_assoc]
          rw [Finset.sum_comm]
          simp only [← Finset.mul_sum, hz, mul_zero, Finset.sum_const_zero]

theorem encoder_rank (q : ℕ) : (encoder q).rank = (4 ^ q - 1) / 3 := by
  apply Nat.le_antisymm _ (rank_lower_of_recovers _ (encoder_recovers q))
  calc
    _ ≤ Fintype.card (ColoredRows q 1) := Matrix.rank_le_card_height _
    _ = _ := by rw [coloredRows_card, if_neg (by decide : (1 : ZMod 3) ≠ 0), add_zero]

/-- A ternary matrix with exactly the optimum number of rows and rank attains
degree zero for every assignment of evaluation points. -/
theorem exact_zero_degree (q : ℕ) (a : Fin q → ℚ) :
    ∃ M : Matrix (Fin ((4 ^ q - 1) / 3)) (Word q) ℚ,
      (∀ i v, M i v = -1 ∨ M i v = 0 ∨ M i v = 1) ∧
      M.rank = (4 ^ q - 1) / 3 ∧ ∃ P, FeasibleZero a M P := by
  classical
  have hc : Fintype.card (ColoredRows q 1) = (4 ^ q - 1) / 3 := by
    rw [coloredRows_card, if_neg (by decide : (1 : ZMod 3) ≠ 0), add_zero]
  let e : ColoredRows q 1 ≃ Fin ((4 ^ q - 1) / 3) :=
    (Fintype.equivFin _).trans (finCongr hc)
  let M : Matrix (Fin ((4 ^ q - 1) / 3)) (Word q) ℚ :=
    (encoder q).reindex e (Equiv.refl _)
  have hr : Recovers M := by
    intro u t z hz hs
    exact encoder_recovers q u t z (fun s => by simpa [M] using hz (e s)) hs
  exact ⟨M, fun i v => encoder_ternary q (e.symm i) v,
    (Matrix.rank_reindex e (Equiv.refl _) (encoder q)).trans (encoder_rank q),
    (feasibleZero_exists_iff a M).mpr hr⟩

/-- The binary degree-zero minimum is the same over all rational matrices and
over ternary matrices. Both are minima of ranks over finite transmissions. -/
theorem exact_minimum_ranks (q : ℕ) (a : Fin q → ℚ) :
    IsLeast {n : ℕ | ∃ (m : ℕ) (M : Matrix (Fin m) (Word q) ℚ) (P : Matrix (Word q) (Word q) ℚ[X]),
        FeasibleZero a M P ∧ M.rank = n} ((4 ^ q - 1) / 3) ∧
    IsLeast {n : ℕ | ∃ (m : ℕ) (M : Matrix (Fin m) (Word q) ℚ) (P : Matrix (Word q) (Word q) ℚ[X]),
        FeasibleZero a M P ∧ (∀ i v, M i v = -1 ∨ M i v = 0 ∨ M i v = 1) ∧ M.rank = n}
      ((4 ^ q - 1) / 3) := by
  obtain ⟨M, hter, hrank, P, hP⟩ := exact_zero_degree q a
  refine ⟨⟨⟨_, M, P, hP, hrank⟩, ?_⟩, ⟨⟨_, M, P, hP, hter, hrank⟩, ?_⟩⟩
  · rintro n ⟨m, N, Q, hQ, rfl⟩
    exact rank_lower_of_feasibleZero hQ
  · rintro n ⟨m, N, Q, hQ, hN, rfl⟩
    exact rank_lower_of_feasibleZero hQ

end Reconstruction.TernaryCode
