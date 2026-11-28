import J8J9GroupedTerm

/- Changes in elaborating imported chart enumerations can flag theorem-scope instances. This affects only the unused-section-variable style linter. -/
set_option linter.unusedSectionVars false

/-! The exact grouped native numerator fits in the centered 10M-bit range.
There are no aggregate or pointwise size hypotheses: the moment, pin,
marked derivative and baseline terms are bounded from the physical chart. -/

namespace J8J9Grouped
open scoped BigOperators Classical
open J8Physical

noncomputable section
variable {Packet R S V G : Type*} {P : V → Type*} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

theorem truth_abs {A : Type*} (F : LiteralPortCompiler.CNF A) (x : A → Bool) :
    |(LiteralPortCompiler.truth F x : ℤ)| ≤ 1 := by
  unfold LiteralPortCompiler.truth LiteralPortCompiler.indicator
  cases LiteralPortCompiler.satisfied F x <;> norm_num

omit [Fintype R] [DecidableEq R] [DecidableEq S] [DecidableEq V] [Fintype Packet] [DecidableEq Packet]
  [(v : V) → Fintype (P v)] [(v : V) → DecidableEq (P v)] in
theorem product_tables_abs (F : OldTables d) (sign : S → Bool) (x : Cube d) :
    |∏ g : G, tablesAt d F sign g (x g)| ≤ 1 := by
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _g : G, (1:ℤ) := by
      apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
      intro g hg
      unfold tablesAt table
      rw [abs_mul, Finset.abs_prod, Finset.abs_prod]
      have h1 : ∏ i : LocalPin d g, |(LiteralPortCompiler.truth
          (LiteralPortCompiler.pin i (sign i.1)) (x g).1 : ℤ)| ≤ 1 := by
        simpa using (Finset.prod_le_prod (s := Finset.univ)
          (g := fun _ : LocalPin d g => (1:ℤ)) (fun _ _ => abs_nonneg _)
          (fun i _ => truth_abs (LiteralPortCompiler.pin i (sign i.1)) (x g).1))
      have h2 : ∏ v : LocalColumn d g, |(LiteralPortCompiler.truth (F g v) ((x g).2 v) : ℤ)| ≤ 1 := by
        simpa using (Finset.prod_le_prod (s := Finset.univ)
          (g := fun _ : LocalColumn d g => (1:ℤ)) (fun _ _ => abs_nonneg _)
          (fun v _ => truth_abs (F g v) ((x g).2 v)))
      exact mul_le_one₀ h1 (by positivity) h2
    _ = _ := by simp

theorem chartRowProduct_eq (a : S) (idx : Wire R ≃ Fin M)
    (j : TargetPorts d a) (hj : j ∈ groupedTargets d a) (x : Cube d) :
    let c := J9End.chart d a idx (fun _ => true)
    let i := J9End.slot d (j.1.1,j.2)
    chartRowProduct d a idx j x =
      J9FactorBounds.difference c i (cubeEquiv d idx x) *
        J9FactorBounds.baseline c i (cubeEquiv d idx x) := by
  dsimp only
  let c := J9End.chart d a idx (fun _ => true)
  let i := J9End.slot d (j.1.1,j.2)
  let bits := cubeEquiv d idx x
  have hwir := (target_slot_spec d a j hj).2
  have hr : c.rowOf i = j.1.1 := congrArg Prod.fst hwir
  have hb : c.leg i = j.2 := congrArg Prod.snd hwir
  let f : R → ℤ := fun r => J8SourceMoment.rowFactor (markedLeg d j r)
    (J9FactorBounds.arg (J9FactorBounds.kernel L) (c.hit r false) (bits (c.rowInput r false)))
    (J9FactorBounds.arg (J9FactorBounds.kernel L) (c.hit r true) (bits (c.rowInput r true)))
  change (∏ r : R, f r) = J9FactorBounds.difference c i bits * J9FactorBounds.baseline c i bits
  rw [← Finset.mul_prod_erase _ f (Finset.mem_univ j.1.1)]
  unfold J9FactorBounds.difference J9FactorBounds.baseline
  rw [hr,hb]
  have hbase : (if c.table bits then (1:ℤ) else 0) = 1 := rfl
  rw [hbase,one_mul]
  congr 1
  · simp only [f,markedLeg,J8SourceMoment.rowFactor,
      J8SourceMoment.selectedEquality_eq,J9FactorBounds.rowDiff_formula]
    cases j.2 <;> rfl
  · apply Finset.prod_congr rfl
    intro r hr
    simp only [f,markedLeg,if_neg (Finset.mem_erase.mp hr).1,J8SourceMoment.rowFactor,
      Option.elim_none,J8SourceMoment.oldEquality_eq,TargetDerivative.equality,
      J9FactorBounds.rowBase,J9FactorBounds.equalityPoly]
    ring

-- Keep the shared physical chart instance bundle across the
-- pointwise and aggregated bounds as the component proofs evolve.
set_option linter.unusedSectionVars false in
theorem groupedTerm_bound (e : EndpointSeating d) (even : Even L) (a : S)
    (off : d.rowLabel (pinWire d a).1 ≠ d.pinLabel a) (idx : Wire R ≃ Fin M)
    (F : OldTables d) (sign : S → Bool) (b : Fin (Fintype.card (PinTile d a)))
    (j : TargetPorts d a) (hj : j ∈ groupedTargets d a) (x : Cube d) (hL : 3 ≤ L) :
    let c := J9End.chart d a idx (fun _ => true)
    |groupedTerm d e even a F sign b j x| ≤
      (2:ℤ)^(((b:ℕ)+1)*L+(2*L+1)+2*L*(J9FactorBounds.activeRows c).card) := by
  dsimp only
  let c := J9End.chart d a idx (fun _ => true)
  let i := J9End.slot d (j.1.1,j.2)
  let bits := cubeEquiv d idx x
  have hT := product_tables_abs d F sign x
  have hS := cubeFeature_bound d a b idx x hL
  have hD := J9FactorBounds.difference_abs_le c i bits (by omega)
  have hB := J9FactorBounds.baseline_abs_le c i bits (by omega)
    (J9End.chart_one_hit d a idx _ e)
  rw [groupedTerm_factored d e even a off idx, chartRowProduct_eq d a idx j hj x]
  simp only [abs_mul, pow_add (2:ℤ) (((b:ℕ)+1)*L+(2*L+1)), pow_add (2:ℤ) (((b:ℕ)+1)*L)]
  have hTS : |∏ g : G, tablesAt d F sign g (x g)| * |feature d a b (x (d.pinLabel a))| ≤
      (2:ℤ)^(((b:ℕ)+1)*L) := by
    simpa using mul_le_mul hT hS (abs_nonneg _) (by decide : (0:ℤ) ≤ 1)
  rw [mul_assoc ((2:ℤ)^_) ((2:ℤ)^_) _]
  exact mul_le_mul hTS (mul_le_mul hD hB (abs_nonneg _) (by positivity))
    (by positivity) (by positivity)

set_option linter.unusedSectionVars false in
set_option maxHeartbeats 500000 in
theorem exactNum_centered (e : EndpointSeating d) (even : Even L) (a : S)
    (off : d.rowLabel (pinWire d a).1 ≠ d.pinLabel a) (idx : Wire R ≃ Fin M)
    (F : OldTables d) (sign : S → Bool) (b : Fin (Fintype.card (PinTile d a)))
    (hL : 3 ≤ L) (hM : L^3 ≤ M) (capacity : L * Fintype.card Packet ≤ 3*M) :
    exactNum d e even a F sign b * 2 ∈
      Set.Ioc (-(2:ℤ)^(10*M)) ((2:ℤ)^(10*M)) := by
  have hEven : L % 2 = 0 := by obtain ⟨k,hk⟩ := even; omega
  have hb : (b:ℕ) < L := by
    have hb := b.isLt
    have hcap := pins_per_tile d a even
    omega
  have hpar (j : TargetPorts d a) (hj : j ∈ groupedTargets d a) :
      (d.seat (j.1.1,j.2)).2.val < L ∧
      (d.seat (j.1.1,j.2)).2.val % 2 = (d.seat (pinWire d a)).2.val % 2 % 2 := by
    have hw : (j.1.1,j.2) ∈ targets d (pinWire d a) := (Finset.mem_filter.mp hj).2
    simpa only [Nat.mod_mod] using
      And.intro (d.seat (j.1.1,j.2)).2.isLt (Finset.mem_filter.mp hw).2.2.1
  have hk := J9End.chart_active_rows_budget d a idx (fun _ => true) capacity
  have hc : |J9FactorBounds.kernel L| ≤ (2:ℤ)^(2*L) := by
    have hh := J9FactorBounds.kernel_budget L (by omega)
    omega
  have h := assignment_term_majorant (groupedTargets d a) (fun j => (d.seat (j.1.1,j.2)).2.val)
    ((d.seat (pinWire d a)).2.val % 2) (J9FactorBounds.kernel L)
    (groupedTerm d e even a F sign b) L b M _
    hL hEven (Nat.mod_lt _ (by decide)) hb hM (groupedTarget_card d a)
    (cube_card d idx).le hk hpar hc
    (fun j hj x => groupedTerm_bound d e even a off idx F sign b j hj x hL)
  rw [exactNum_as_sum d e even a off F sign b]
  exact h

#print axioms chartRowProduct_eq
#print axioms groupedTerm_bound
#print axioms exactNum_centered
end
end J8J9Grouped
