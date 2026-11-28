import J6R52FreshExteriorWordsGlue

/-! There need not be an old Setup containing placeholder words. This
is the source attachment constructor with precisely the unrelated
fields, a public numeric code bound, and the paid register producer. -/
namespace J6R52FreshExterior
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost
open J6Mesh J6OrientedHost J7R10Plant J6R30GeneratedRootLayout
open J6R26StablePreparedRoot J6R34RootAtlas J6R30ProducedGateRegistry J6R27PrescribedProbe
open J6R24LegalLayout J6R24MeteredRecursion
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 13000000
set_option maxRecDepth 2800

noncomputable section
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q r c d edgew tc tj key prec tw bw : ℕ}

structure SetupOutsideWords (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
    (J6R28GeneratedRootFrame.constantRootWord m))
    (ell edgew tc tj key tw bw : ℕ) where
  positive : 0<ell
  field : Meter (J6R24MeteredRecursion.Frame f (J6SourcePrecision.printed m base))
  hf : f.Monic
  centre : J6Recovery.Addr m
  sample : Fin (sampleCount f ell m base n native T)
  group : Fin 64
  address : OccurrenceAddress tc tj
  timeOK : address.centre.val=index m centre
  sampleOK : address.sample.val=sample.val
  groupOK : address.group.val=group.val
  edgePos : 0<edgew
  edgeFit : (J6R32RootGeneratedRegistryInputs.exteriorChild G ell centre sample group).edges<2^edgew
  issue : Meter (Word key)
  code : ℕ
  codeBound : rootCodeWidth m base≤code
  context : CentreContext tw bw
  signedCentre : context.center=(index m centre:ℤ)
  codeTruth : context.codeWidth.val=code

variable (S : SetupOutsideWords G ell edgew tc tj key tw bw)

def setupFromProducedWords (W : ExteriorRegisters q prec)
    (C : W.copies.val=K m) (P : W.pre.val=J6SourcePrecision.printed m base)
    (B : W.birth.val=J6SourcePrecision.printed m base) :
    Setup G ell q edgew tc tj key prec tw bw where
  positive := S.positive
  field := S.field
  hf := S.hf
  centre := S.centre
  sample := S.sample
  group := S.group
  address := S.address
  timeOK := S.timeOK
  sampleOK := S.sampleOK
  groupOK := S.groupOK
  edgePos := S.edgePos
  edgeFit := S.edgeFit
  issue := S.issue
  birth := W.birth
  birthOK := B
  hq := Nat.zero_lt_one.trans (copy_width_above_one (C ▸ val_lt W.copies))
  qFits := copy_width_above_one (C ▸ val_lt W.copies)
  copies := W.copies
  pre := W.pre
  copiesOK := C
  precOK := P
  copyFits := copies_fit_root_key m
  code := S.code
  codePos := (root_code_positive m base).trans_le S.codeBound
  context := S.context
  signedCentre := S.signedCentre
  codeTruth := S.codeTruth

def attachWithRetainedPaidWords {s : ℕ}
    (portFile : LiteralPortFile T r c d) (retained : Word s)
    (tag : retained.val=J6SourcePrecision.printed m base)
    (copyFit : K m<2^q) (preFit : J6SourcePrecision.printed m base<2^q)
    (birthFit : J6SourcePrecision.printed m base<2^prec) :
    Meter (StableExterior G ell q r c d edgew tc tj key prec tw bw) :=
  let W := makeExteriorRegisters m q prec retained
  let H := made_exterior_registers_exact m base q prec retained tag copyFit preFit birthFit
  let A := setupFromProducedWords S W.result H.1 H.2.1 H.2.2.1
  ⟨attachLiteralWithPublicWidth A portFile S.codeBound, W.steps+8⟩

theorem retained_paid_words_attached_same_occurrence {s : ℕ}
    (portFile : LiteralPortFile T r c d) (retained : Word s)
    (tag : retained.val=J6SourcePrecision.printed m base)
    (copyFit : K m<2^q) (preFit : J6SourcePrecision.printed m base<2^q)
    (birthFit : J6SourcePrecision.printed m base<2^prec) :
    let R := attachWithRetainedPaidWords S portFile retained tag copyFit preFit birthFit
    let W := makeExteriorRegisters m q prec retained
    R.result.source.raw=portFile.raw ∧ R.result.centre=S.centre ∧ R.result.sample=S.sample ∧
      R.result.group=S.group ∧ R.result.address=S.address ∧ R.result.issue=S.issue ∧
      R.result.field=S.field ∧ R.result.copies=W.result.copies ∧
      R.result.pre=W.result.pre ∧ R.result.birth=W.result.birth ∧
      R.steps=exteriorRegistersFee s q prec+8 := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  exact congrArg (fun n : ℕ=>n+8)
    (made_exterior_registers_exact m base q prec retained tag copyFit preFit birthFit).2.2.2

#print axioms setupFromProducedWords
#print axioms attachWithRetainedPaidWords
#print axioms retained_paid_words_attached_same_occurrence
end
end J6R52FreshExterior

