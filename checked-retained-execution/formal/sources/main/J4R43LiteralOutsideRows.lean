import J4R43LiteralOutsideMatch
import V8NativeMessageN7LiteralSupportColumnRows

/-! Eliminating the actual subdivision equalities in the old-column
orientation uses the same physical shift. A graph-only common band makes
each equality see at most one nonzero argument. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9PacketTiles
open Paper5.HybridClosure Paper5.D1Literal V8NativeMessage.N7LiteralSupport
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
variable {W : Type} [Fintype W] [DecidableEq W]
variable (F : Finset (W×W)) (reg : ∀ v, GraphCutMoments.degree F v=3)
variable {a : ℕ} {R : Type} [CommRing R]
local notation "E" => DWire F
local notation "D" => MainClonedCNF.Port F
variable (P : PhysicalPacking (oldColumnNetwork F reg) a (Fin 64))

theorem subdivision_has_unmatched_leg {h : ℕ} (G : BandCertificate P h) {t : ℤ}
    (wide : 2^a-h≤t.natAbs) (q : D) :
    ¬rowHit P t (q,false) ∨ ¬rowHit P t (q,true) := by
  by_cases yes : rowHit P t (q,false)
  · right
    intro yes'
    have hsame := single_row_hit P G wide yes yes' rfl
    exact Bool.false_ne_true (congrArg Prod.snd hsame)
  · exact Or.inl yes

theorem actual_argument_unmatched (t : ℤ) (κ : R) (y : E→Bool) (r : E)
    (h : ¬rowHit P t r) : actualColumnArgument F reg P t κ y r=0 := by
  unfold actualColumnArgument
  rw [literal_unmatched_port_zero P t _ r (fun q hq=>h ⟨q,hq⟩),mul_zero]

theorem real_row_weight_factors {h : ℕ} (G : BandCertificate P h) {t : ℤ}
    (wide : 2^a-h≤t.natAbs) (κ : R) (y : E→Bool) (q : D) :
    literalSubdivisionWeight F reg P t κ y q =
      sourceRowWeight P t κ y (q,false)*sourceRowWeight P t κ y (q,true) := by
  change equalityPair (actualColumnArgument F reg P t κ y (q,false))
    (actualColumnArgument F reg P t κ y (q,true)) =
      (1-actualColumnArgument F reg P t κ y (q,false))*(1-actualColumnArgument F reg P t κ y (q,true))
  rcases subdivision_has_unmatched_leg F reg P G wide q with miss|miss
  · rw [actual_argument_unmatched F reg P t κ y _ miss]
    simp [equalityPair]
  · rw [actual_argument_unmatched F reg P t κ y _ miss]
    simp [equalityPair]

theorem real_row_factors_transfer_to_columns {h : ℕ} (G : BandCertificate P h) {t : ℤ}
    (wide : 2^a-h≤t.natAbs) (κ : R) (y : E→Bool) :
    (∏ q : D, literalSubdivisionWeight F reg P t κ y q) =
      ∏ q : E,sourceColumnWeight P t κ y q := by
  calc
    _ = ∏ q : D,sourceRowWeight P t κ y (q,false)*sourceRowWeight P t κ y (q,true) :=
      Finset.prod_congr rfl (fun q _=>real_row_weight_factors F reg P G wide κ y q)
    _ = ∏ q : E, sourceRowWeight P t κ y q := by
      rw [Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun q _=>?_
      rw [Fintype.prod_bool,mul_comm]
    _ = _ := (row_product_over_matches P t κ y).trans (match_product_over_columns P t κ y)

theorem actual_flat_after_band {h : ℕ} (G : BandCertificate P h) {t : ℤ}
    (wide : 2^a-h≤t.natAbs) (κ : R) (σ : W→Bool) :
    flatSigned P t κ (oldColumnTruth F reg σ) =
       ∑ y : E→Bool, if originalColumnKeep F reg σ y then
         ∏ q : E,sourceColumnWeight P t κ y q else 0 := by
  rw [actual_old_column_rows_summed F reg P t κ σ]
  refine Finset.sum_congr rfl fun y _=>?_
  rw [real_row_factors_transfer_to_columns F reg P G wide κ y]

#print axioms subdivision_has_unmatched_leg
#print axioms actual_argument_unmatched
#print axioms real_row_weight_factors
#print axioms real_row_factors_transfer_to_columns
#print axioms actual_flat_after_band
end
end J4R43LiteralOutside

