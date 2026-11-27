import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Nat.Find
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.RingTheory.Ideal.Maps

open Matrix

namespace GrenetMcCoy

variable {R ρ κ : Type*} [CommRing R] [Fintype κ] [DecidableEq κ]

/-- Test all ordered row selections. A repeated row has zero determinant,
so these are exactly the full-column minors with harmless extra zeros. -/
def KillsFullMinors (A : Matrix ρ κ R) (r : R) : Prop :=
  ∀ rows : κ → ρ, r * (A.submatrix rows id).det = 0

theorem killsFullMinors_iff_injective_rows (A : Matrix ρ κ R) (r : R) :
    KillsFullMinors A r ↔
      ∀ rows : κ → ρ, Function.Injective rows → r * (A.submatrix rows id).det = 0 := by
  refine ⟨fun h rows _ => h rows, ?_⟩
  intro h rows
  by_cases hi : Function.Injective rows
  · exact h rows hi
  · obtain ⟨i, j, hrow, hne⟩ := Function.not_injective_iff.mp hi
    rw [Matrix.det_zero_of_row_eq hne (funext fun c => by simp [hrow]), mul_zero]

/-- A coordinate of a kernel vector annihilates all full-column minors. -/
theorem kernel_coordinate_kills_full_minors (A : Matrix ρ κ R) (v : κ → R)
    (hv : A *ᵥ v = 0) (j : κ) : KillsFullMinors A (v j) := by
  intro rows
  let B := A.submatrix rows id
  have hB : B *ᵥ v = 0 := by
    funext i
    exact congrFun hv (rows i)
  have h := congrArg (fun w : κ → R => B.adjugate *ᵥ w) hB
  change B.adjugate *ᵥ (B *ᵥ v) = B.adjugate *ᵥ (0 : κ → R) at h
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_zero] at h
  simpa [Pi.smul_apply, smul_eq_mul, mul_comm, B] using congrFun h j

/-- The scaled cofactor vector on an extended minor gives a kernel vector.
The added column has coordinate r times the distinguished k-minor. -/
private theorem cofactor_kernel (A : Matrix ρ κ R) (r : R) {k : ℕ}
    (rows : Fin k → ρ) (cols : Fin (k + 1) → κ) (hcols : Function.Injective cols)
    (hnz : r * (A.submatrix rows (cols ∘ Fin.succ)).det ≠ 0)
    (hzero : ∀ i, r * (A.submatrix (Fin.cons i rows) cols).det = 0) :
    ∃ x : κ → R, x ≠ 0 ∧ A *ᵥ x = 0 := by
  classical
  let w (j : Fin (k + 1)) : R :=
    r * ((-1) ^ j.val * (A.submatrix rows (cols ∘ j.succAbove)).det)
  let x (j : κ) : R := ∑ q, if cols q = j then w q else 0
  refine ⟨x, ?_, ?_⟩
  · intro hx
    have h := congrFun hx (cols 0)
    exact hnz (by simpa [x, hcols.eq_iff, w, Fin.succAbove_zero] using h)
  · funext i
    calc
      (A *ᵥ x) i = ∑ q, A i (cols q) * w q := by
        change (∑ j, A i j * ∑ q, if cols q = j then w q else 0) = _
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun q _ => by simp [mul_ite]
      _ = r * (A.submatrix (Fin.cons i rows) cols).det := by
        rw [Matrix.det_succ_row_zero, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hd : (A.submatrix (Fin.cons i rows) cols).submatrix Fin.succ j.succAbove =
            A.submatrix rows (cols ∘ j.succAbove) := by
          ext p q
          rfl
        rw [hd]
        change A i (cols j) * (r * ((-1) ^ j.val * _)) =
          r * ((-1) ^ j.val * A i (cols j) * _)
        ring
      _ = 0 := hzero i

/-- McCoy's constructive direction. A nonzero common annihilator yields
a nonzero kernel vector via a largest surviving scaled minor. -/
theorem exists_kernel_of_kills_full_minors (A : Matrix ρ κ R) (r : R) (hr : r ≠ 0)
    (hkill : KillsFullMinors A r) : ∃ x : κ → R, x ≠ 0 ∧ A *ᵥ x = 0 := by
  classical
  let survives (k : ℕ) : Prop :=
    ∃ (rows : Fin k → ρ) (cols : Fin k → κ), r * (A.submatrix rows cols).det ≠ 0
  let n := Fintype.card κ
  let k := Nat.findGreatest survives n
  have hbase : survives 0 := ⟨Fin.elim0, Fin.elim0, by simpa using hr⟩
  obtain ⟨rows, cols, hnz⟩ :=
    (show survives k from Nat.findGreatest_spec (Nat.zero_le n) hbase)
  have hc : Function.Injective cols := by
    by_contra h
    obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp h
    apply hnz
    rw [Matrix.det_zero_of_column_eq hne (fun z => by simp [hij]), mul_zero]
  have hk : k < n := lt_of_le_of_ne (Nat.findGreatest_le n) (fun he => by
    have hb := (Fintype.bijective_iff_injective_and_card cols).mpr ⟨hc, by simpa using he⟩
    let e := Equiv.ofBijective cols hb
    have hm : (A.submatrix rows cols).submatrix e.symm e.symm =
        A.submatrix (rows ∘ e.symm) id := by
      ext i j
      change A (rows (e.symm i)) (e (e.symm j)) = A (rows (e.symm i)) j
      rw [e.apply_symm_apply]
    have hz := hkill (rows ∘ e.symm)
    rw [← hm, Matrix.det_submatrix_equiv_self] at hz
    exact hnz hz)
  have hnext : ¬ survives (k + 1) :=
    Nat.findGreatest_is_greatest (Nat.lt_succ_self k) hk
  obtain ⟨c, hcOut⟩ : ∃ c : κ, c ∉ Set.range cols := by
    by_contra! hall
    have hsurj : Function.Surjective cols := hall
    exact (not_le_of_gt hk) (by simpa using Fintype.card_le_of_surjective cols hsurj)
  let v : Fin (k + 1) → κ := Fin.cons c cols
  have hv : Function.Injective v := Fin.cons_injective_of_injective hcOut hc
  refine cofactor_kernel A r rows v hv ?_ ?_
  · exact hnz
  · intro i
    by_contra h
    exact hnext ⟨Fin.cons i rows, v, h⟩

/-- McCoy's criterion for a matrix over any commutative ring with one. -/
theorem mulVec_injective_iff_full_minor_annihilator (A : Matrix ρ κ R) :
    Function.Injective A.mulVec ↔ ∀ r : R, KillsFullMinors A r → r = 0 := by
  constructor
  · intro hinj r hr
    by_contra hn
    obtain ⟨x, hx, hzero⟩ := exists_kernel_of_kills_full_minors A r hn hr
    exact hx (hinj (hzero.trans (Matrix.mulVec_zero A).symm))
  · intro h x y hxy
    apply sub_eq_zero.mp
    have hzero : A *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    funext j
    exact h _ (kernel_coordinate_kills_full_minors A (x - y) hzero j)

/-- The ideal generated by the full-column minors. -/
def fullMinorIdeal (A : Matrix ρ κ R) : Ideal R :=
  Ideal.span (Set.range fun rows : κ → ρ => (A.submatrix rows id).det)

theorem mem_fullMinorIdeal_annihilator (A : Matrix ρ κ R) (r : R) :
    r ∈ (fullMinorIdeal A).annihilator ↔ KillsFullMinors A r := by
  rw [fullMinorIdeal, ← Ideal.submodule_span_eq, Submodule.mem_annihilator_span]
  constructor
  · intro h rows
    exact h ⟨_, ⟨rows, rfl⟩⟩
  · rintro h ⟨_, rows, rfl⟩
    exact h rows

theorem mulVec_injective_iff_fullMinorIdeal_annihilator_eq_bot (A : Matrix ρ κ R) :
    Function.Injective A.mulVec ↔ (fullMinorIdeal A).annihilator = ⊥ := by
  rw [mulVec_injective_iff_full_minor_annihilator, eq_bot_iff]
  exact ⟨fun h r hr => Ideal.mem_bot.mpr (h r ((mem_fullMinorIdeal_annihilator A r).mp hr)),
    fun h r hr => Ideal.mem_bot.mp (h ((mem_fullMinorIdeal_annihilator A r).mpr hr))⟩

/-- With fewer rows than columns there are no full-column minors with
distinct rows, and any nonzero ring supplies a nonzero kernel vector. -/
theorem exists_kernel_of_fewer_rows [Fintype ρ] [Nontrivial R] (A : Matrix ρ κ R)
    (h : Fintype.card ρ < Fintype.card κ) :
    ∃ x : κ → R, x ≠ 0 ∧ A *ᵥ x = 0 := by
  apply exists_kernel_of_kills_full_minors A 1 one_ne_zero
  apply (killsFullMinors_iff_injective_rows A 1).mpr
  intro rows hrows
  exact False.elim ((not_le_of_gt h) (Fintype.card_le_of_injective rows hrows))

end GrenetMcCoy
