import ColorAlphabetTensor
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open scoped BigOperators

namespace Reconstruction.ColorAlphabet

variable {R G : Type*} [Fintype R] [DecidableEq R] [AddCommGroup G] [DecidableEq G]

private abbrev Fiber (color : R → G) (q : ℕ) (g : G) :=
  {s : Fin q → R // totalColor color s = g}

omit [Fintype R] [DecidableEq R] [DecidableEq G] in
private theorem color_cons (color : R → G) {q : ℕ} (k : R) (s : Fin q → R) :
    totalColor color (Fin.cons k s) = color k + totalColor color s := by
  simp [totalColor, Fin.sum_univ_succ]

private def splitFiber (color : R → G) (q : ℕ) (g : G) :
    (Σ s : Fin q → R, {k : R // color k = g - totalColor color s}) ≃ Fiber color (q + 1) g where
  toFun p := ⟨Fin.cons p.2.val p.1, by rw [color_cons, p.2.property, sub_add_cancel]⟩
  invFun s := ⟨Fin.tail s.val, ⟨s.val 0, by
    apply eq_sub_of_add_eq
    rw [← color_cons, Fin.cons_self_tail]
    exact s.property⟩⟩
  left_inv := by
    rintro ⟨s, k⟩
    simp
  right_inv s := by
    apply Subtype.ext
    exact Fin.cons_self_tail _

private theorem convolution_succ (color : R → G) (m d : ℕ)
    (hcolor : ∀ g, Fintype.card {k // color k = g} = m + if g = 0 then d else 0)
    (q : ℕ) (g : G) :
    Fintype.card (Fiber color (q + 1) g) =
      m * Fintype.card R ^ q + d * Fintype.card (Fiber color q g) := by
  classical
  have hif (s : Fin q → R) : (g - totalColor color s = 0) ↔ totalColor color s = g :=
    sub_eq_zero.trans eq_comm
  rw [← Fintype.card_congr (splitFiber color q g), Fintype.card_sigma]
  simp only [hcolor, hif, Finset.sum_add_distrib, ← Finset.sum_filter,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Fintype.card_fun, Fintype.card_fin, Nat.mul_comm m, Nat.mul_comm d,
    Fintype.subtype_card]
  simp

private def baseCount (N m d : ℕ) : ℕ → ℕ
  | 0 => 0
  | q + 1 => m * N ^ q + d * baseCount N m d q

private theorem fiber_count_base (color : R → G) (m d : ℕ)
    (hcolor : ∀ g, Fintype.card {k // color k = g} = m + if g = 0 then d else 0)
    (q : ℕ) (g : G) :
    Fintype.card (Fiber color q g) =
      baseCount (Fintype.card R) m d q + if g = 0 then d ^ q else 0 := by
  classical
  induction q generalizing g with
  | zero =>
    by_cases hg : g = 0
    · subst g
      let e : Fiber color 0 0 ≃ (Fin 0 → R) :=
        { toFun := Subtype.val
          invFun := fun s => ⟨s, by simp [totalColor]⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      rw [Fintype.card_congr e]
      simp [baseCount]
    · letI : IsEmpty (Fiber color 0 g) :=
        ⟨fun s => hg (s.property.symm.trans (by simp [totalColor]))⟩
      simp [hg, baseCount]
  | succ q ih =>
    rw [convolution_succ color m d hcolor, ih, baseCount]
    by_cases hg : g = 0 <;> simp [hg, pow_succ] <;> ring

private theorem baseCount_identity (N p m d : ℕ) (hN : N = p*m+d) (q : ℕ) :
    p * baseCount N m d q + d ^ q = N ^ q := by
  induction q with
  | zero => simp [baseCount]
  | succ q ih =>
    rw [baseCount, pow_succ d, pow_succ N]
    calc
      _ = p*m*N^q + d*(p*baseCount N m d q + d^q) := by ring
      _ = N ^ q * N := by rw [ih, hN]; ring

theorem color_fiber_card (color : R → G) (p m d : ℕ) (hp : 0 < p)
    (hN : Fintype.card R = p*m+d)
    (hcolor : ∀ g, Fintype.card {k // color k = g} = m + if g = 0 then d else 0)
    (q : ℕ) (g : G) :
    Fintype.card (Fiber color q g) =
      (Fintype.card R ^ q - d ^ q) / p + if g = 0 then d ^ q else 0 := by
  rw [fiber_count_base color m d hcolor]
  have h := baseCount_identity (Fintype.card R) p m d hN q
  rw [← h, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hp]

theorem color_rows_card (color : R → G) (p m d : ℕ) (hp : 0 < p)
    (hN : Fintype.card R = p*m+d)
    (hcolor : ∀ g, Fintype.card {k // color k = g} = m + if g = 0 then d else 0)
    [Fintype G] (accept : G → Prop) [DecidablePred accept] (hzero : ¬ accept 0)
    (q : ℕ) :
    Fintype.card (ColorRows q color accept) =
      Fintype.card {g // accept g} * ((Fintype.card R ^ q - d ^ q) / p) := by
  classical
  let e : (Σ g : {g // accept g}, Fiber color q g.val) ≃ ColorRows q color accept :=
    { toFun := fun g => ⟨g.2.val, g.2.property.symm ▸ g.1.property⟩
      invFun := fun s => ⟨⟨totalColor color s.val, s.property⟩, ⟨s.val, rfl⟩⟩
      left_inv := by
        rintro ⟨⟨g, hg⟩, ⟨s, hs⟩⟩
        change totalColor color s = g at hs
        subst g
        rfl
      right_inv := fun _ => rfl }
  rw [← Fintype.card_congr e, Fintype.card_sigma]
  simp_rw [color_fiber_card color p m d hp hN hcolor]
  have hnonzero (g : {g // accept g}) : g.val ≠ 0 := fun e => hzero (e ▸ g.property)
  simp [hnonzero, Finset.sum_const]

end Reconstruction.ColorAlphabet
