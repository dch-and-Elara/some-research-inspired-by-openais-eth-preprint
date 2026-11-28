import J6R52FreshExteriorWordsRetained
import J6R52FreshExteriorSetup

/-! Supply the actual Setup/attach binder without a materialized roster
premise. The numeric code guard is independent of the compact source
file. Other setup data (including selected occurrence) is unchanged. -/
namespace J6R52FreshExterior
open scoped Classical Polynomial
open Polynomial J6Mesh J6OrientedHost J6R24LegalLayout J6R26StablePreparedRoot
open J6R31RootResidentTables J6R30GeneratedRootLayout J6R15ModeCost AOracleMachineTime
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 12000000

noncomputable section
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q r c d edgew tc tj key prec tw bw : ℕ}
variable (D : Setup G ell q edgew tc tj key prec tw bw)

theorem code_fit_of_public_numeric_bound (bound : rootCodeWidth m base≤D.code)
    (raw : List (SignedHalfPort r c d)) :
    1+(writeResidents m D.hq (oddAxis m) D.copies D.pre raw).result.roster.modes.length<2^D.code := by
  have fit := printed_root_code_fit m base D.hq D.qFits D.copies D.pre D.copiesOK D.precOK raw
  exact fit.trans_le (Nat.pow_le_pow_right (by decide) bound)

def attachLiteralWithPublicWidth (C : LiteralPortFile T r c d) (bound : rootCodeWidth m base≤D.code) :
    J6R34RootAtlas.StableExterior G ell q r c d edgew tc tj key prec tw bw :=
  attachLiteral D C (code_fit_of_public_numeric_bound D bound C.raw)

theorem attached_public_width_keeps_same_file
    (C : LiteralPortFile T r c d) (bound : rootCodeWidth m base≤D.code) :
    (attachLiteralWithPublicWidth D C bound).source.raw=C.raw := rfl

def replaceRetainedSetupWords {s : ℕ} (input : Word s)
    (printed : input.val=J6SourcePrecision.printed m base)
    (copiesFit : K m<2^q) (preFit : J6SourcePrecision.printed m base<2^q)
    (stampFit : J6SourcePrecision.printed m base<2^prec) :
    Meter (Setup G ell q edgew tc tj key prec tw bw) :=
  let R := makeExteriorRegisters m q prec input
  let e := made_exterior_registers_exact m base q prec input printed copiesFit preFit stampFit
  ⟨{ D with
      birth := R.result.birth
      birthOK := e.2.2.1
      copies := R.result.copies
      copiesOK := e.1
      pre := R.result.pre
      precOK := e.2.1
      copyFits := copies_fit_root_key m },R.steps+4⟩

theorem refreshed_paid_words_exact {s : ℕ} (input : Word s)
    (printed : input.val=J6SourcePrecision.printed m base)
    (copiesFit : K m<2^q) (preFit : J6SourcePrecision.printed m base<2^q)
    (stampFit : J6SourcePrecision.printed m base<2^prec) :
    let R := makeExteriorRegisters m q prec input
    let A := replaceRetainedSetupWords D input printed copiesFit preFit stampFit
    A.result.copies=R.result.copies ∧ A.result.pre=R.result.pre ∧ A.result.birth=R.result.birth ∧
      A.result.centre=D.centre ∧ A.result.sample=D.sample ∧ A.result.group=D.group ∧
      A.steps=exteriorRegistersFee s q prec+4 := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  exact congrArg (fun n : ℕ=>n+4)
    (made_exterior_registers_exact m base q prec input printed copiesFit preFit stampFit).2.2.2

#print axioms code_fit_of_public_numeric_bound
#print axioms attached_public_width_keeps_same_file
#print axioms refreshed_paid_words_exact
end
end J6R52FreshExterior
