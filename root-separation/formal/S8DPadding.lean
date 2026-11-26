import S8Certificates
import MainIncidence

namespace S8

open scoped BigOperators
open SourceDensity

variable {W I A : Type*} [Fintype W] [Fintype I] [DecidableEq I] [Fintype A]
  [DecidableEq A] [Nonempty A]

/-- Equal per-cell capacity for the paper's packet construction. We may include
    one extra empty block when the maximum already is divisible by L. -/
noncomputable def paddedLoad (cell : W → (I → A) × (I → A)) (L : ℕ) : ℕ :=
  ((Finset.univ.sup (fiberCount cell)) / L + 1) * L

omit [Nonempty A] in
theorem padded_load_max (cell : W → (I → A) × (I → A)) (L : ℕ) (hL : 0 < L) :
    ∀ c, fiberCount cell c ≤ paddedLoad cell L := by
  intro c
  let n := Finset.univ.sup (fiberCount cell)
  have hu : fiberCount cell c ≤ n := Finset.le_sup (Finset.mem_univ c)
  have h := Nat.mod_add_div n L
  have hm := Nat.mod_lt n hL
  unfold paddedLoad
  change _ ≤ (n / L + 1) * L
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm (n / L) L]
  omega

theorem padded_load_budget (cell : W → (I → A) × (I → A)) (Δ : ℚ)
    (cert : CollisionCertificate cell Δ) (L : ℕ) (hL : 0 < L)
    (feasible : L * Fintype.card ((I → A) × (I → A)) ≤ Fintype.card W) :
    (paddedLoad cell L : ℚ) ≤ 3 * Fintype.card W / Fintype.card ((I → A) × (I → A)) := by
  classical
  let D := (Fintype.card ((I → A) × (I → A)) : ℚ)
  let M := (Fintype.card W : ℚ)
  let n := Finset.univ.sup (fiberCount cell)
  have hc : 0 < D := by dsimp [D]; positivity
  have hmax : (n : ℚ) ≤ 2 * M / D := by
    obtain ⟨c, _, hc⟩ := Finset.exists_mem_eq_sup
      (s := (Finset.univ : Finset ((I → A) × (I → A))))
      Finset.univ_nonempty (fiberCount cell)
    change n = fiberCount cell c at hc
    rw [hc]
    exact port_cell_bound cell Δ cert c
  have hround : paddedLoad cell L ≤ n + L := by
    rw [paddedLoad, Nat.add_mul, Nat.one_mul]
    exact Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
  have hr : (paddedLoad cell L : ℚ) ≤ n + (L : ℚ) := by exact_mod_cast hround
  have hL' : (L : ℚ) ≤ M / D := (le_div_iff₀ hc).2 (by dsimp [D,M]; exact_mod_cast feasible)
  change _ ≤ 3 * M / D
  exact hr.trans ((add_le_add hmax hL').trans_eq (by ring))

/-- Numerical root packet capacity. Existence of an oriented slot embedding is
    a separate combinatorial statement. -/
theorem packet_count_budget (cell : W → (I → A) × (I → A)) (Δ : ℚ)
    (cert : CollisionCertificate cell Δ) (L : ℕ) (hL : 0 < L)
    (feasible : L * Fintype.card ((I → A) × (I → A)) ≤ Fintype.card W) :
    ((paddedLoad cell L / L * Fintype.card ((I → A) × (I → A)) : ℕ) : ℚ) ≤
      3 * Fintype.card W / L := by
  have h := padded_load_budget cell Δ cert L hL feasible
  let D := (Fintype.card ((I → A) × (I → A)) : ℚ)
  have hc : 0 < D := by dsimp [D]; positivity
  have hd : (0 : ℚ) < L := by exact_mod_cast hL
  apply (le_div_iff₀ hd).2
  have hc' := (le_div_iff₀ hc).1 h
  have hp : ((paddedLoad cell L / L : ℕ) : ℚ) * L ≤ paddedLoad cell L := by
    exact_mod_cast Nat.div_mul_le_self (paddedLoad cell L) L
  push_cast
  change ((paddedLoad cell L / L : ℕ) : ℚ) * D * L ≤ _
  nlinarith only [hc', mul_le_mul_of_nonneg_right hp hc.le]

/-- Padded capacity of all cells with a specified row or column symbol. -/
theorem symbol_port_budget (cell : W → (I → A) × (I → A)) (Δ : ℚ)
    (cert : CollisionCertificate cell Δ) (L : ℕ) (hL : 0 < L)
    (feasible : L * Fintype.card ((I → A) × (I → A)) ≤ Fintype.card W)
    (j : I) (b : Bool) (g : A) :
    (paddedLoad cell L : ℚ) *
      fiberCount (fun c : (I → A) × (I → A) => (if b then c.2 else c.1) j) g ≤
        3 * Fintype.card W / Fintype.card A := by
  let proj (c : (I → A) × (I → A)) := (if b then c.2 else c.1) j
  let m := Fintype.card A ^ (Fintype.card I - 1) * Fintype.card A ^ Fintype.card I
  have hp (a : A) : fiberCount proj a = m := by
    cases b
    · exact BalancedUnion.single_coordinate_fiber j a
    · exact MainIncidence.factor_symbol_fiber j a
  have hc : (Fintype.card ((I → A) × (I → A)) : ℚ) = Fintype.card A * (m : ℚ) := by
    exact_mod_cast regular_projection_card proj m hp
  have ha : (0 : ℚ) < Fintype.card A := by positivity
  change (paddedLoad cell L : ℚ) * fiberCount proj g ≤ _
  rw [hp, le_div_iff₀ ha]
  have h := (le_div_iff₀ (by positivity : (0 : ℚ) < Fintype.card ((I → A) × (I → A)))).1
    (padded_load_budget cell Δ cert L hL feasible)
  rw [hc] at h
  simpa only [mul_left_comm, mul_assoc, mul_comm] using h

#print axioms symbol_port_budget
#print axioms padded_load_max
#print axioms padded_load_budget
#print axioms packet_count_budget

end S8

