import EmpiricalCutMoments

/-! The numerical root packing certificate bounds actual full-cell loads.
Injecting pin vertices into the ports and projecting equal-size collections
of cells then bounds the empirical law of their labels. -/

namespace SourceDensity

open scoped BigOperators

variable {V P C X : Type*}

def fiberCount {S T : Type*} [Fintype S] [DecidableEq T] (f : S → T) (t : T) : ℕ :=
  (Finset.univ.filter fun s => f s = t).card

/-- One-coordinate consequence of the two numerical inequalities (B). -/
theorem numeric_cell_bound [Fintype C] (Xload : C → ℚ) (M Q Δ : ℚ)
    (hM : 0 ≤ M) (hQ : 0 < Q)
    (hcollision : (∑ c, (Xload c - M / Q) ^ 2) ≤ 2 * M * Δ)
    (hfeasible : 2 * Q ^ 2 * Δ ≤ M) (c : C) : Xload c ≤ 2 * M / Q := by
  have hs : (Xload c - M / Q) ^ 2 ≤ 2 * M * Δ :=
    (Finset.single_le_sum (fun a (_ : a ∈ (Finset.univ : Finset C)) =>
      sq_nonneg (Xload a - M / Q)) (Finset.mem_univ c)).trans hcollision
  have hsmall : 2 * M * Δ ≤ (M / Q) ^ 2 := by
    rw [div_pow]
    apply (le_div_iff₀ (sq_pos_of_pos hQ)).2
    nlinarith only [mul_le_mul_of_nonneg_left hfeasible hM]
  have habs : |Xload c - M / Q| ≤ M / Q :=
    (sq_le_sq₀ (abs_nonneg _) (div_nonneg hM hQ.le)).mp
      (by simpa only [sq_abs] using hs.trans hsmall)
  have hu := (le_abs_self (Xload c - M / Q)).trans habs
  rw [mul_div_assoc]
  linarith only [hu]

variable [Fintype P] [Fintype C] [DecidableEq C]

/-- The certificate uses the number of ports as M, the number of possible full
cells as Q, and the actual number of ports in each such cell as its load. -/
structure CollisionCertificate (cell : P → C) (Δ : ℚ) : Prop where
  collision : (∑ c, ((fiberCount cell c : ℚ) - Fintype.card P / (Fintype.card C : ℚ)) ^ 2) ≤
    2 * (Fintype.card P : ℚ) * Δ
  feasible : 2 * (Fintype.card C : ℚ) ^ 2 * Δ ≤ Fintype.card P

theorem port_cell_bound [Nonempty C] (cell : P → C) (Δ : ℚ)
    (cert : CollisionCertificate cell Δ) (c : C) :
    (fiberCount cell c : ℚ) ≤ 2 * Fintype.card P / (Fintype.card C : ℚ) :=
  numeric_cell_bound _ _ _ Δ (Nat.cast_nonneg _) (by exact_mod_cast Fintype.card_pos (α := C))
    cert.collision cert.feasible c

section Projection

variable [Fintype X] [DecidableEq X]

omit [Fintype X] in
theorem fiberCount_comp (cell : P → C) (proj : C → X) (x : X) :
    fiberCount (fun p => proj (cell p)) x =
      ∑ c ∈ Finset.univ.filter (fun c => proj c = x), fiberCount cell c := by
  simpa [fiberCount] using
    (Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset P)
      (Finset.univ.filter fun c => proj c = x) cell).symm

omit [Fintype X] in
theorem fiberCount_injection [Fintype V] (pin : V ↪ P) (L : P → X) (x : X) :
    fiberCount (fun v => L (pin v)) x ≤ fiberCount L x := by
  apply Finset.card_le_card_of_injOn pin _ pin.injective.injOn
  intro v hv
  change v ∈ Finset.univ.filter (fun w : V => L (pin w) = x) at hv
  change pin v ∈ Finset.univ.filter (fun p : P => L p = x)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hv).2⟩

omit [DecidableEq C] in
theorem regular_projection_card (proj : C → X) (m : ℕ) (hreg : ∀ x, fiberCount proj x = m) :
    Fintype.card C = Fintype.card X * m := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset C)) (t := (Finset.univ : Finset X)) (f := proj)
    (fun _ _ => Finset.mem_univ _)
  change (Finset.univ : Finset C).card = ∑ x, fiberCount proj x at h
  simpa [hreg] using h

theorem projected_port_bound [Nonempty C] [Nonempty X] (cell : P → C) (Δ : ℚ)
    (cert : CollisionCertificate cell Δ) (proj : C → X) (m : ℕ) (hreg : ∀ x, fiberCount proj x = m)
    (x : X) :
    (fiberCount (fun p => proj (cell p)) x : ℚ) ≤ 2 * Fintype.card P / (Fintype.card X : ℚ) := by
  have hc : (Fintype.card C : ℚ) = (Fintype.card X : ℚ) * m := by
    exact_mod_cast regular_projection_card proj m hreg
  have hc0 : (Fintype.card C : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hx0 : (Fintype.card X : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [fiberCount_comp, Nat.cast_sum]
  calc
    _ ≤ ∑ _c ∈ Finset.univ.filter (fun c => proj c = x),
        2 * Fintype.card P / (Fintype.card C : ℚ) :=
      Finset.sum_le_sum fun c _ => port_cell_bound cell Δ cert c
    _ = (m : ℚ) * (2 * Fintype.card P / (Fintype.card C : ℚ)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      change (fiberCount proj x : ℚ) * _ = _
      rw [hreg]
    _ = _ := by
      apply (eq_div_iff hx0).2
      calc
        _ = (2 * Fintype.card P / (Fintype.card C : ℚ)) * (Fintype.card X * (m : ℚ)) := by ring
        _ = _ := by rw [← hc, div_mul_cancel₀ _ hc0]

theorem pin_marginal_bound [Fintype V] [Nonempty V]
    (pin : V ↪ P) (cell : P → C) (Δ : ℚ) (cert : CollisionCertificate cell Δ)
    (proj : C → X) (m : ℕ) (hreg : ∀ x, fiberCount proj x = m) (x : X) :
    EmpiricalCutMoments.empiricalLaw (fun v => proj (cell (pin v))) x ≤
      (2 * Fintype.card P / (Fintype.card V : ℚ)) * ProductVariance.uniformWeight X := by
  letI : Nonempty C := Nonempty.map (fun v => cell (pin v)) ‹Nonempty V›
  letI : Nonempty X := Nonempty.map proj ‹Nonempty C›
  have hx : (fiberCount (fun v => proj (cell (pin v))) x : ℚ) ≤
      (fiberCount (fun p => proj (cell p)) x : ℚ) := by
    exact_mod_cast fiberCount_injection pin (fun p => proj (cell p)) x
  have hv : (0 : ℚ) < Fintype.card V := by exact_mod_cast Fintype.card_pos (α := V)
  change (fiberCount (fun v => proj (cell (pin v))) x : ℚ) / (Fintype.card V : ℚ) ≤ _
  calc
    _ ≤ (2 * Fintype.card P / (Fintype.card X : ℚ)) / Fintype.card V :=
      (div_le_div_iff_of_pos_right hv).2 ((hx.trans (projected_port_bound cell Δ cert proj m hreg x)))
    _ = _ := by unfold ProductVariance.uniformWeight; ring

theorem pin_marginal_twenty [Fintype V] [Nonempty V]
    (pin : V ↪ P) (cell : P → C) (Δ : ℚ) (cert : CollisionCertificate cell Δ)
    (proj : C → X) (m : ℕ) (hreg : ∀ x, fiberCount proj x = m)
    (hports : Fintype.card P = 10 * Fintype.card V) (x : X) :
    EmpiricalCutMoments.empiricalLaw (fun v => proj (cell (pin v))) x ≤
      20 * ProductVariance.uniformWeight X := by
  have hv : (Fintype.card V : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hratio : 2 * (Fintype.card P : ℚ) / Fintype.card V = 20 := by
    apply (div_eq_iff hv).2
    have hp : (Fintype.card P : ℚ) = 10 * (Fintype.card V : ℚ) := by exact_mod_cast hports
    linarith only [hp]
  simpa only [hratio] using pin_marginal_bound pin cell Δ cert proj m hreg x

end Projection

/-- Project a complete coordinate tuple onto the kept coordinates. -/
def projectCoordinates {U T A : Type*} (z : U ⊕ T → A) (u : U) : A := z (Sum.inl u)

private def projectionFiberEquiv {U T A : Type*} (x : U → A) :
    {z : U ⊕ T → A // projectCoordinates z = x} ≃ (T → A) where
  toFun z t := z.1 (Sum.inr t)
  invFun rest := ⟨Sum.elim x rest, rfl⟩
  left_inv := by
    intro z
    apply Subtype.ext
    funext c
    cases c with
    | inl u => exact (congrFun z.2 u).symm
    | inr t => rfl
  right_inv _ := rfl

theorem coordinate_projection_regular {U T A : Type*} [Fintype U] [DecidableEq U]
    [Fintype T] [DecidableEq T] [Fintype A] [DecidableEq A] (x : U → A) :
    fiberCount (projectCoordinates (T := T)) x = (Fintype.card A) ^ (Fintype.card T) := by
  classical
  rw [fiberCount, ← Fintype.card_subtype, Fintype.card_congr (projectionFiberEquiv (T := T) x),
    Fintype.card_fun]

/-- A full source cell is the ordered pair of labels on the two port sides.
Keep any specified set of coordinates of the first label. -/
def firstCoordinates {I A : Type*} (kept : Finset I) (cell : (I → A) × (I → A)) : kept → A :=
  fun i => cell.1 i.1

private def orderedCellFiberEquiv {I A : Type*} [DecidableEq I] (kept : Finset I) (x : kept → A) :
    {cell : (I → A) × (I → A) // firstCoordinates kept cell = x} ≃
      (({i // i ∉ kept} → A) × (I → A)) where
  toFun z := (fun i => z.1.1 i.1, z.1.2)
  invFun free := ⟨(fun i => if h : i ∈ kept then x ⟨i,h⟩ else free.1 ⟨i,h⟩, free.2), by
    funext i
    simp [firstCoordinates, i.2]⟩
  left_inv := by
    rintro ⟨⟨u,v⟩, hx⟩
    apply Subtype.ext
    apply Prod.ext
    · funext i
      by_cases h : i ∈ kept
      · simpa [h] using (congrFun hx ⟨i,h⟩).symm
      · simp [h]
    · rfl
  right_inv := by
    intro free
    apply Prod.ext
    · funext i
      simp [i.2]
    · rfl

theorem ordered_cell_projection_regular {I A : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] [DecidableEq A] (kept : Finset I) (x : kept → A) :
    fiberCount (firstCoordinates kept) x =
      (Fintype.card A) ^ (Fintype.card I - kept.card) * (Fintype.card A) ^ (Fintype.card I) := by
  classical
  rw [fiberCount, ← Fintype.card_subtype, Fintype.card_congr (orderedCellFiberEquiv kept x),
    Fintype.card_prod, Fintype.card_fun, Fintype.card_fun, Fintype.card_subtype_compl,
    Fintype.card_coe]

theorem source_pin_marginal_twenty {I A : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] [DecidableEq A] [Fintype V] [Nonempty V]
    (pin : V ↪ P) (cell : P → (I → A) × (I → A)) (Δ : ℚ)
    (cert : CollisionCertificate cell Δ) (hports : Fintype.card P = 10 * Fintype.card V)
    (kept : Finset I) (x : kept → A) :
    EmpiricalCutMoments.empiricalLaw (fun v => firstCoordinates kept (cell (pin v))) x ≤
      20 * ProductVariance.uniformWeight (kept → A) :=
  pin_marginal_twenty pin cell Δ cert (firstCoordinates kept) _
    (ordered_cell_projection_regular kept) hports x

#print axioms numeric_cell_bound
#print axioms port_cell_bound
#print axioms fiberCount_comp
#print axioms fiberCount_injection
#print axioms regular_projection_card
#print axioms projected_port_bound
#print axioms pin_marginal_bound
#print axioms pin_marginal_twenty
#print axioms coordinate_projection_regular
#print axioms ordered_cell_projection_regular
#print axioms source_pin_marginal_twenty

end SourceDensity
