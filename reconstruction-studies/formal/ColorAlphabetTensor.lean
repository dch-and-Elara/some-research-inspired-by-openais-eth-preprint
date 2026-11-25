import ColorAlphabetModel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace Reconstruction.ColorAlphabet

variable {L R G F : Type*} [Fintype L] [DecidableEq L]
  [Fintype R] [DecidableEq R] [AddCommGroup G] [DecidableEq G] [Field F]

def totalColor (color : R → G) {q : ℕ} (s : Fin q → R) : G := ∑ t, color (s t)

abbrev ColorRows (q : ℕ) (color : R → G) (accept : G → Prop) :=
  {s : Fin q → R // accept (totalColor color s)}

def tensorRows (e : R → L × L → F) (q : ℕ) (color : R → G)
    (accept : G → Prop) : Matrix (ColorRows q color accept) (Word (fun _ : Fin q => L)) F :=
  fun s v => ∏ t, e (s.val t) (v t)

omit [Fintype R] [DecidableEq R] [DecidableEq G] in
private theorem insert_color (color : R → G) {q : ℕ} (t : Fin (q + 1))
    (s : Fin q → R) (k : R) :
    totalColor color (t.insertNth k s) = color k + totalColor color s := by
  rw [totalColor, Fin.sum_univ_succAbove _ t]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, totalColor]

omit [Fintype L] in
private theorem product_delta {q : ℕ} (u v : Word (fun _ : Fin q => L)) :
    (∏ i, if u i = v i then (1 : F) else 0) = if u = v then 1 else 0 := by
  by_cases h : u = v
  · simp [h]
  · obtain ⟨i, hi⟩ : ∃ i, u i ≠ v i := by
      by_contra! he
      exact h (funext he)
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- Local coordinate expansions and recovery by each allowed translate yield simultaneous
recovery by the single collection of allowed tensor rows. -/
theorem tensorRows_recovers (e : R → L × L → F) (color : R → G) (accept : G → Prop)
    [DecidablePred accept] (q : ℕ)
    (expand : ∀ u : L × L, ∃ b : R → F, ∀ v,
      ∑ k, b k * e k v = if u = v then 1 else 0)
    (decode : ∀ (g : G) (u : L × L), ∃ d : R → F,
      (∀ k, ¬ accept (color k + g) → d k = 0) ∧
      ∀ v, v.1 ≠ u.2 → ∑ k, d k * e k v = if u = v then 1 else 0) :
    Recovers (tensorRows e q color accept) := by
  classical
  choose b hb using expand
  choose d hds hde using decode
  intro u t z hz hs
  cases q with
  | zero => exact Fin.elim0 t
  | succ q =>
    let coefficient (s : Fin q → R) (k : R) : F :=
      d (totalColor color s) (u t) k * ∏ i, b (u (t.succAbove i)) (s i)
    let row (s : Fin q → R) (k : R) (v : Word (fun _ : Fin (q + 1) => L)) : F :=
      ∏ j, e (Fin.insertNth (α := fun _ => R) t k s j) (v j)
    have hrow (s : Fin q → R) (k : R) :
        ∑ v, (coefficient s k * row s k v) * z v = 0 := by
      by_cases h : accept (color k + totalColor color s)
      · let sk : ColorRows (q + 1) color accept := ⟨t.insertNth k s, by rwa [insert_color]⟩
        simp_rw [mul_assoc, ← Finset.mul_sum]
        change coefficient s k * (∑ v, tensorRows e (q + 1) color accept sk v * z v) = 0
        rw [hz sk, mul_zero]
      · simp [coefficient, hds _ _ _ h]
    have hdelta (v : Word (fun _ : Fin (q + 1) => L)) (hv : (v t).1 ≠ (u t).2) :
        (∑ s, ∑ k, coefficient s k * row s k v) = if u = v then 1 else 0 := by
      have term (s : Fin q → R) (k : R) :
          coefficient s k * row s k v =
            (d (totalColor color s) (u t) k * e k (v t)) *
              ∏ i, b (u (t.succAbove i)) (s i) * e (s i) (v (t.succAbove i)) := by
        dsimp only [coefficient, row]
        rw [Fin.prod_univ_succAbove _ t]
        simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
        rw [Finset.prod_mul_distrib]
        ring
      simp only [term, ← Finset.sum_mul, hde _ _ _ hv, ← Finset.mul_sum]
      rw [← Fintype.prod_sum (fun (i : Fin q) k => b (u (t.succAbove i)) k * e k (v (t.succAbove i)))]
      simp only [hb]
      rw [← Fin.prod_univ_succAbove (fun i => if u i = v i then (1 : F) else 0) t, product_delta]
    calc
      z u = ∑ v, (if u = v then 1 else 0) * z v := by simp [ite_mul]
      _ = ∑ v, (∑ s, ∑ k, coefficient s k * row s k v) * z v := by
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : (v t).1 = (u t).2
        · simp [hs v hv]
        · rw [hdelta v hv]
      _ = 0 := by
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_eq_zero
        intro s _
        rw [Finset.sum_comm]
        simp only [hrow, Finset.sum_const_zero]

end Reconstruction.ColorAlphabet
