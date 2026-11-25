import BareissSolverMinors

open scoped BigOperators

namespace Reconstruction.BareissSolver

/-- Keep the pivot first, followed by the selected indices of the reduced table. -/
def insertPick {n k : ℕ} (j : Fin (n+1)) (c : Fin k ↪ Fin n) : Fin (k+1) ↪ Fin (n+1) :=
  ⟨Fin.cons j (j.succAbove ∘ c), by
    intro u
    refine Fin.cases ?_ (fun u => ?_) u <;> intro v <;> refine Fin.cases ?_ (fun v => ?_) v
    · intro _; rfl
    · intro h
      exact (Fin.succAbove_ne j (c v) (by simpa using h.symm)).elim
    · intro h
      simp only [Fin.cons_zero, Fin.cons_succ, Function.comp_apply] at h
      exact (Fin.succAbove_ne j (c u) h).elim
    · intro h
      simp only [Fin.cons_succ, Function.comp_apply] at h
      exact congrArg Fin.succ (c.injective (Fin.succAbove_right_injective (p := j) h))⟩

@[simp] theorem insertPick_zero {n k : ℕ} (j : Fin (n+1)) (c : Fin k ↪ Fin n) : insertPick j c 0 = j := by
  simp [insertPick]

@[simp] theorem insertPick_succ {n k : ℕ} (j : Fin (n+1)) (c : Fin k ↪ Fin n) (v : Fin k) :
    insertPick j c v.succ = j.succAbove (c v) := by simp [insertPick]

theorem restore_supported {m n k : ℕ} (A : Coefficients (m+1) (n+1)) (b : Column (m+1))
    (i : Fin (m+1)) (j : Fin (n+1)) (c : Fin k ↪ Fin n) (x : Column n)
    (hx : ∀ v, v ∉ Set.range c → x v = 0) :
    ∀ v, v ∉ Set.range (insertPick j c) → restore A b i j x v = 0 := by
  intro v
  induction v using Fin.succAboveCases j with
  | x => intro h; exact (h ⟨0, insertPick_zero j c⟩).elim
  | p v =>
    intro h
    rw [restore_other]
    apply hx
    rintro ⟨u, rfl⟩
    exact h ⟨u.succ, insertPick_succ j c u⟩

theorem det_insertPick {m n k : ℕ} (A : Coefficients (m+1) (n+1))
    (i : Fin (m+1)) (j : Fin (n+1)) (h : A i j ≠ 0)
    (rs : Fin k ↪ Fin m) (cs : Fin k ↪ Fin n) :
    (A.submatrix (insertPick i rs) (insertPick j cs)).det =
      A i j * ((stepMatrix A i j).submatrix rs cs).det := by
  have hh := det_bordered_step A 0 i j h rs (some ∘ cs)
  have hcs : (Fin.cons (some j) (Option.map j.succAbove ∘ some ∘ cs)) = some ∘ insertPick j cs := by
    funext v
    refine Fin.cases ?_ (fun w => ?_) v <;> simp
  change ((augmented A 0).submatrix (insertPick i rs)
    (Fin.cons (some j) (Option.map j.succAbove ∘ (some ∘ cs)))).det = _ at hh
  rw [show (Option.map j.succAbove ∘ (some ∘ cs)) = Option.map j.succAbove ∘ some ∘ cs from rfl, hcs] at hh
  exact hh

/-- A determinant ratio for each pivot coordinate. The same integer
denominator is used for all pivot coordinates, and each numerator is an
ordered minor of the original augmented matrix. -/
theorem MinorFrame.cramer {m₀ n₀ m n depth k : ℕ} {Z : IntegerAugment m₀ n₀} {d D : ℤ}
    {A : Coefficients m n} {b : Column m} (F : MinorFrame Z depth d A b)
    (rs : Fin k ↪ Fin m) (cs : Fin k ↪ Fin n) {x : Column n}
    (hx : Solves A b x) (hzero : ∀ j, j ∉ Set.range cs → x j = 0)
    (hdet : (d:ℚ)*(A.submatrix rs cs).det = D) (j : Fin k) :
    ∃ a : ℤ, HasMinor Z (depth+k) a ∧ (a:ℚ) = (D:ℚ)*x (cs j) := by
  classical
  let N : Matrix (Fin k) (Fin k) ℚ := A.submatrix rs cs
  let col : Fin k → Option (Fin n) := fun u => if u = j then none else some (cs u)
  have hsum (i : Fin k) : (∑ u, x (cs u) • N i u) = b (rs i) := by
    simp only [N, Matrix.submatrix_apply, smul_eq_mul]
    simp_rw [mul_comm (x (cs _))]
    calc
      _ = ∑ v ∈ Finset.univ.map cs, A (rs i) v * x v := by rw [Finset.sum_map]
      _ = _ := (Finset.sum_subset (Finset.subset_univ _) fun v _ hv => by
        have hn : v ∉ Set.range cs := by simpa using hv
        rw [hzero v hn, mul_zero]).trans (hx (rs i))
  have heq : (augmented A b).submatrix rs col = N.updateCol j (fun i => ∑ u, x (cs u) • N i u) := by
    ext i u
    by_cases hu : u = j
    · subst u
      simpa [col, smul_eq_mul] using (hsum i).symm
    · simp [col, hu, N]
  obtain ⟨a, ha, he⟩ := F.minor k rs col
  refine ⟨a,ha,?_⟩
  rw [he, heq, Matrix.det_updateCol_sum, smul_eq_mul, ← hdet]
  ring

end Reconstruction.BareissSolver
