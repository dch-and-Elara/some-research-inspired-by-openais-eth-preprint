import J6R52FreshExteriorWordsComputed
import J6R52FreshExteriorWordsShell

/-! A no-template true exterior attachment when even the printed
precision tape is not supplied: the only numeric tape input here
is the public base precision. Unrelated site setup is explicit. -/
namespace J6R52FreshExterior
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost
open J6Mesh J6OrientedHost J7R10Plant J6R30GeneratedRootLayout
open J6R26StablePreparedRoot J6R34RootAtlas J6R24LegalLayout J6R24MeteredRecursion
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 13500000
set_option maxRecDepth 2850

noncomputable section
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q r c d edgew tc tj key prec tw bw : ℕ}
variable (S : SetupOutsideWords G ell edgew tc tj key tw bw)

def attachWithComputedPaidWords
    (portFile : LiteralPortFile T r c d) (baseWord : Word q) (tag : baseWord.val=base)
    (copyFit : K m<2^q) (preFit : J6SourcePrecision.printed m base<2^q)
    (birthFit : J6SourcePrecision.printed m base<2^prec) :
    Meter (StableExterior G ell q r c d edgew tc tj key prec tw bw) :=
  let W := computeExteriorRegisters m prec baseWord
  let H := computed_exterior_registers_exact m base prec baseWord tag copyFit preFit birthFit
  let A := setupFromProducedWords S W.result H.1 H.2.1 H.2.2.1
  ⟨attachLiteralWithPublicWidth A portFile S.codeBound, W.steps+8⟩

theorem computed_paid_words_attached_same_occurrence
    (portFile : LiteralPortFile T r c d) (baseWord : Word q) (tag : baseWord.val=base)
    (copyFit : K m<2^q) (preFit : J6SourcePrecision.printed m base<2^q)
    (birthFit : J6SourcePrecision.printed m base<2^prec) :
    let R := attachWithComputedPaidWords S portFile baseWord tag copyFit preFit birthFit
    let W := computeExteriorRegisters m prec baseWord
    R.result.source.raw=portFile.raw ∧ R.result.centre=S.centre ∧ R.result.sample=S.sample ∧
      R.result.group=S.group ∧ R.result.address=S.address ∧ R.result.issue=S.issue ∧
      R.result.field=S.field ∧ R.result.copies=W.result.copies ∧
      R.result.pre=W.result.pre ∧ R.result.birth=W.result.birth ∧
      R.steps=((precisionFromBaseWord m (modeWordAsA baseWord)).steps+exteriorRegistersFee q q prec+4)+8 := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  exact congrArg (fun n : ℕ=>n+8)
    (computed_exterior_registers_exact m base prec baseWord tag copyFit preFit birthFit).2.2.2

#print axioms attachWithComputedPaidWords
#print axioms computed_paid_words_attached_same_occurrence
end
end J6R52FreshExterior

