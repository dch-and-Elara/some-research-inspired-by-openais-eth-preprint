import J8J9GroupedRows

/-! Integer, assignment-wise expansion of the actual marked grouped term. -/

namespace J8J9Grouped
open scoped BigOperators Classical
open J8Physical

noncomputable section
variable {Packet R S V G : Type*} {P : V → Type*} {L M : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S]
variable [Fintype V] [DecidableEq V] [Fintype G] [DecidableEq G] [Fintype Packet] [DecidableEq Packet]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

def tablesAt (F : OldTables d) (sign : S → Bool) (g : G) (x : Assignment d g) : ℤ :=
  (∏ i : LocalPin d g, LiteralPortCompiler.truth (R := ℤ)
    (LiteralPortCompiler.pin i (sign i.1)) x.1) * table d F g x.2

def summand (e : EndpointSeating d) (even : Even L) (F : OldTables d) (sign : S → Bool)
    (g : G) (mark : Option (LocalRow d g × Bool)) (feat : Assignment d g → ℤ)
    (x : Assignment d g) : ℤ :=
  tablesAt d F sign g x * feat x *
    ∏ r : LocalRow d g, J8SourceMoment.rowFactor (J8SourceMoment.marker mark r)
      (argument d e even g x r false) (argument d e even g x r true)

omit [Fintype G] [Fintype Packet] [DecidableEq Packet] in
theorem child_as_sum (e : EndpointSeating d) (even : Even L) (F : OldTables d) (sign : S → Bool)
    (g : G) (mark : Option (LocalRow d g × Bool)) (feat : Assignment d g → ℤ) :
    child d e even F sign g mark feat = ∑ x : Assignment d g, summand d e even F sign g mark feat x := by
  unfold child integerChild
  change _ = ∑ x : (LocalPin d g → Bool) × LocalBits d g, _
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro pins hp
  dsimp [summand,tablesAt]
  ring

def groupedTerm (e : EndpointSeating d) (even : Even L) (a : S) (F : OldTables d) (sign : S → Bool)
    (b : Fin (Fintype.card (PinTile d a))) (j : TargetPorts d a) (x : Cube d) : ℤ :=
  ∏ g : G, insertSpecial (fun g => summand d e even F sign g none (fun _ => 1))
    (d.pinLabel a) (d.rowLabel (pinWire d a).1)
    (summand d e even F sign _ none (feature d a b))
    (summand d e even F sign _ (some j) (fun _ => 1)) g (x g)

omit [Fintype Packet] in
theorem exactNum_as_sum (e : EndpointSeating d) (even : Even L) (a : S)
    (off : d.rowLabel (pinWire d a).1 ≠ d.pinLabel a) (F : OldTables d) (sign : S → Bool)
    (b : Fin (Fintype.card (PinTile d a))) :
    exactNum d e even a F sign b =
      CompletedPrecisionBudget.cleared (groupedTargets d a) Finset.univ
        (physicalDen d a b) (fun _ => J9FactorBounds.slope L b) (groupedTerm d e even a F sign b) := by
  simp only [exactNum, pub, child_as_sum]
  exact numerator_as_assignment_sum _ _ _ _ _ _ off.symm _ _

def markedLeg (j : TargetPorts d a) (r : R) : Option Bool := if r = j.1.1 then some j.2 else none

def chartRowProduct (a : S) (idx : Wire R ≃ Fin M) (j : TargetPorts d a) (x : Cube d) : ℤ :=
  let c := J9End.chart d a idx (fun _ => true)
  ∏ r : R, J8SourceMoment.rowFactor (markedLeg d j r)
    (J9FactorBounds.arg (J9FactorBounds.kernel L) (c.hit r false)
      (cubeEquiv d idx x (c.rowInput r false)))
    (J9FactorBounds.arg (J9FactorBounds.kernel L) (c.hit r true)
      (cubeEquiv d idx x (c.rowInput r true)))

set_option linter.unusedSectionVars false in
omit [DecidableEq S] [DecidableEq V] [(v : V) → DecidableEq (P v)] in
theorem groupedTerm_factored (e : EndpointSeating d) (even : Even L) (a : S)
    (off : d.rowLabel (pinWire d a).1 ≠ d.pinLabel a) (idx : Wire R ≃ Fin M)
    (F : OldTables d) (sign : S → Bool)
    (b : Fin (Fintype.card (PinTile d a))) (j : TargetPorts d a) (x : Cube d) :
    groupedTerm d e even a F sign b j x =
      ((∏ g : G, tablesAt d F sign g (x g)) * feature d a b (x (d.pinLabel a))) *
        chartRowProduct d a idx j x := by
  let gs := d.pinLabel a
  let gt := d.rowLabel (pinWire d a).1
  let c := J9End.chart d a idx (fun _ => true)
  let v : R → ℤ := fun r => J8SourceMoment.rowFactor (markedLeg d j r)
    (J9FactorBounds.arg (J9FactorBounds.kernel L) (c.hit r false)
      (cubeEquiv d idx x (c.rowInput r false)))
    (J9FactorBounds.arg (J9FactorBounds.kernel L) (c.hit r true)
      (cubeEquiv d idx x (c.rowInput r true)))
  let w : G → ℤ := fun g => if g = gs then feature d a b (x gs) else 1
  have hgroup (g : G) :
    insertSpecial (fun g => summand d e even F sign g none (fun _ => 1))
        gs gt (summand d e even F sign _ none (feature d a b))
        (summand d e even F sign _ (some j) (fun _ => 1)) g (x g) =
        tablesAt d F sign g (x g) * w g * ∏ r : LocalRow d g, v r.1 := by
      have hr (r : LocalRow d g) (leg : Bool) := argument_eq_chart d e even a idx
        (fun _ => true) x g r leg
      by_cases hs : g = gs
      · subst g
        simp only [insertSpecial, dif_pos True.intro, summand, w, if_pos rfl]
        congr 1
        apply Finset.prod_congr rfl
        intro r _
        have hne : r.val ≠ j.1.val := by
          intro h
          exact off (j.1.property.symm.trans ((congrArg d.rowLabel h).symm.trans r.property))
        simp only [v,markedLeg,if_neg hne,J8SourceMoment.marker,Option.bind_none,hr]
        rfl
      · by_cases ht : g = gt
        · subst g
          simp only [insertSpecial, dif_neg hs, dif_pos True.intro, summand, w, if_neg hs]
          congr 1
          apply Finset.prod_congr rfl
          intro r _
          rw [hr,hr]
          change J8SourceMoment.rowFactor (J8SourceMoment.marker (some j) r) _ _ =
            J8SourceMoment.rowFactor (markedLeg d j r.val) _ _
          congr 1
          by_cases he : r = j.1
          · subst r; simp [J8SourceMoment.marker, markedLeg]
          · have hn : r.val ≠ j.1.val := fun h => he (Subtype.ext h)
            simp [J8SourceMoment.marker, markedLeg, hn, Ne.symm he]
        · simp only [insertSpecial, dif_neg hs, dif_neg ht, summand, w, if_neg hs]
          congr 1
          apply Finset.prod_congr rfl
          intro r _
          have hne : r.val ≠ j.1.val := by
            intro h
            exact ht (r.property.symm.trans ((congrArg d.rowLabel h).trans j.1.property))
          simp only [v,markedLeg,if_neg hne,J8SourceMoment.marker,Option.bind_none,hr]
          rfl
  have hw : (∏ g : G, w g) = feature d a b (x gs) := by
    rw [Finset.prod_eq_single gs]
    · simp [w]
    · intro g _ hn
      simp [w,hn]
    · simp
  unfold groupedTerm
  rw [Finset.prod_congr rfl (fun g _ => hgroup g), Finset.prod_mul_distrib,
    Finset.prod_mul_distrib, hw, grouped_row_product d v]
  rfl

#print axioms child_as_sum
#print axioms exactNum_as_sum
#print axioms groupedTerm_factored
end
end J8J9Grouped
