
import J6R24LegalLayoutBudget
import J6R25StableCensusCard
import J6R25StableCensusCompactRoot
import P11FullPackingChart

/-! Actual root readout widths are computable from its printed padded
geometry. No resident padding list or input claim about its length is
needed to select these word widths. -/
namespace J6R28GeneratedRootFrame
open J6Mesh J6R24LegalLayout J6R25StableCensus J6R22RootReadout P11FullPacking
set_option maxHeartbeats 4500000
set_option linter.unusedSectionVars false

def literalPadCount (m : ℕ) := (D m*K m-m)*printedHalf m

theorem literal_cell_card (m : ℕ) : Fintype.card (CellType (a m))=D m := by
  change Fintype.card (Cell (Fin (a m)) (Fin 64))=D m
  rw [←Nat.card_eq_fintype_card,total_cells,Fintype.card_fin]
  exact cell_palette m

theorem literal_pad_count (m : ℕ) (w : Fin (a m)→Fin 64) :
    (exactPadOrder m (K m) (printedHalf m) w).length=literalPadCount m := by
  rw [actual_pad_tape_count m (K m) (printedHalf m) w (printed_room m),literal_cell_card]
  rfl

theorem literal_pad_count_source (m : ℕ) : 2*literalPadCount m=M m-m*L m := by
  unfold literalPadCount
  calc
    2*((D m*K m-m)*printedHalf m) = (D m*K m-m)*(2*printedHalf m) := by ring
    _ = _ := by rw [printed_half_correct,Nat.sub_mul,mul_assoc,mesh_product]

theorem literal_pad_count_half (m : ℕ) : literalPadCount m=(M m-m*L m)/2 := by
  rw [←literal_pad_count_source m]
  omega

def printedFactorWidth (m q : ℕ) := publicFactorWidth m q (literalPadCount m)+2

def printedAnswerWidth (m base : ℕ) :=
  (baseTermWidth m (outerMeshWidth m) (J6SourcePrecision.printed m base)+1)*(m+1)+3

theorem printed_readout_fits (m q base : ℕ) (w : Fin (a m)→Fin 64) :
    0<printedFactorWidth m q ∧ 0<printedAnswerWidth m base ∧
    publicFactorWidth m q (exactPadOrder m (K m) (printedHalf m) w).length+2≤printedFactorWidth m q ∧
    (baseTermWidth m (outerMeshWidth m) (J6SourcePrecision.printed m base)+1)*(m+1)+3≤printedAnswerWidth m base := by
  refine ⟨by unfold printedFactorWidth; omega,by unfold printedAnswerWidth; omega,?_,le_rfl⟩
  rw [literal_pad_count,printedFactorWidth]

#print axioms literal_cell_card
#print axioms literal_pad_count
#print axioms literal_pad_count_source
#print axioms literal_pad_count_half
#print axioms printed_readout_fits
end J6R28GeneratedRootFrame
