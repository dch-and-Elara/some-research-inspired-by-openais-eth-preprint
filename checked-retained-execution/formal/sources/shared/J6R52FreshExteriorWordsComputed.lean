import J6R52FreshExteriorWordsArithmetic

/-! The setup words can also be produced with no retained printed
precision tape: compute it from the actual base bit word, then charge
the three register writes and prove the independent menu bound. -/
namespace J6R52FreshExterior
open scoped Classical
open J6Mesh J6R15ModeCost J6R24LegalLayout J6R31RootResidentTables J6R30GeneratedRootLayout
open AOracleMachineTime AOracleMachineTimeTape
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 12800000

def modeWordAsA {q : ℕ} (w : Word q) : A1R10.Word q := ⟨w.bits,w.size⟩

def aWordAsMode {q : ℕ} (w : A1R10.Word q) : Word q := ⟨w.val,w.property⟩

def computeExteriorRegisters {q : ℕ} (m prec : ℕ) (baseWord : Word q) :
    Meter (ExteriorRegisters q prec) :=
  let P := precisionFromBaseWord m (modeWordAsA baseWord)
  let R := makeExteriorRegisters m q prec (aWordAsMode P.result)
  ⟨R.result,P.steps+R.steps+4⟩

theorem computed_exterior_registers_exact {q : ℕ} (m base prec : ℕ) (baseWord : Word q)
    (orig : baseWord.val=base) (copiesFit : K m<2^q)
    (preFit : J6SourcePrecision.printed m base<2^q)
    (birthFit : J6SourcePrecision.printed m base<2^prec) :
    let R := computeExteriorRegisters m prec baseWord
    R.result.copies.val=K m ∧ R.result.pre.val=J6SourcePrecision.printed m base ∧
      R.result.birth.val=J6SourcePrecision.printed m base ∧
      R.steps=(precisionFromBaseWord m (modeWordAsA baseWord)).steps+exteriorRegistersFee q q prec+4 := by
  let P := precisionFromBaseWord m (modeWordAsA baseWord)
  have H : (aWordAsMode P.result).val=J6SourcePrecision.printed m base :=
    precision_from_base_word_exact m base (modeWordAsA baseWord) orig preFit
  obtain ⟨a,b,c,d⟩ := made_exterior_registers_exact m base q prec (aWordAsMode P.result)
    H copiesFit preFit birthFit
  refine ⟨a,b,c,?_⟩
  change P.steps+(makeExteriorRegisters m q prec (aWordAsMode P.result)).steps+4=_
  rw [d]

theorem computed_exterior_has_numeric_code_fit {q r c d : ℕ}
    (m base prec : ℕ) (baseWord : Word q) (orig : baseWord.val=base)
    (copiesFit : K m<2^q) (preFit : J6SourcePrecision.printed m base<2^q)
    (birthFit : J6SourcePrecision.printed m base<2^prec)
    (raw : List (SignedHalfPort r c d)) :
    let R := computeExteriorRegisters m prec baseWord
    1+(writeResidents m ((copy_width_above_one copiesFit).trans' (by decide))
      (oddAxis m) R.result.copies R.result.pre raw).result.roster.modes.length<2^rootCodeWidth m base := by
  obtain ⟨C,P,_,_⟩ := computed_exterior_registers_exact m base prec baseWord orig copiesFit preFit birthFit
  exact printed_root_code_fit m base _ (copy_width_above_one copiesFit) _ _ C P raw

#print axioms computed_exterior_registers_exact
#print axioms computed_exterior_has_numeric_code_fit
end J6R52FreshExterior
