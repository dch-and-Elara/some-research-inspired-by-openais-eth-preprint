import J6R34RootAtlasStable

/-! Construct the actual selected Appendix-D exterior job from a
fresh literal port file, rather than assuming a frozen chart.  Frame
and integer word setup remain separately supplied and metered. -/
namespace J6R52FreshExterior
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost
open J6Mesh J6OrientedHost J7R10Plant J6R30GeneratedRootLayout
open J6R26StablePreparedRoot J6R34RootAtlas J6R27PrescribedProbe J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R20Ancestor J6R21Ancestor
open J6R12Blueprint J6R17ModeTape J6R31RootResidentTables J6R32RootGeneratedRegistryInputs

open J6R24LegalLayout J6R24MeteredRecursion

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3200
set_option maxHeartbeats 17500000
set_option linter.unusedSectionVars false

noncomputable section
variable {V : Type} [Fintype V]
variable {f : ℤ[X]} {m n base native : ℕ} {T : Plant V m n}
variable (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
  (J6R28GeneratedRootFrame.constantRootWord m))

structure Setup (G : RootShape f m (printedHalf m) base native (printedRankWidth m) T
    (J6R28GeneratedRootFrame.constantRootWord m))
    (ell q edgew tc tj key prec tw bw : ℕ) where
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
  edgeFit : (exteriorChild G ell centre sample group).edges<2^edgew
  issue : Meter (Word key)
  birth : Word prec
  birthOK : birth.val=J6SourcePrecision.printed m base
  hq : 0<q
  qFits : 1<q
  copies : Word q
  pre : Word q
  copiesOK : copies.val=K m
  precOK : pre.val=J6SourcePrecision.printed m base
  copyFits : K m≤2^RootKey m
  code : ℕ
  codePos : 0<code
  context : CentreContext tw bw
  signedCentre : context.center=(index m centre:ℤ)
  codeTruth : context.codeWidth.val=code

variable {G} {ell q rr cc dd edgew tc tj key prec tw bw : ℕ}
variable (D : Setup G ell q edgew tc tj key prec tw bw)

def attachLiteral (C : LiteralPortFile T rr cc dd)
    (codeFits : 1+(writeResidents m D.hq (oddAxis m) D.copies D.pre C.raw).result.roster.modes.length<2^D.code) :
    StableExterior G ell q rr cc dd edgew tc tj key prec tw bw where
  positive := D.positive
  field := D.field
  hf := D.hf
  source := C
  centre := D.centre
  sample := D.sample
  group := D.group
  address := D.address
  timeOK := D.timeOK
  sampleOK := D.sampleOK
  groupOK := D.groupOK
  edgePos := D.edgePos
  edgeFit := D.edgeFit
  issue := D.issue
  birth := D.birth
  birthOK := D.birthOK
  hq := D.hq
  qFits := D.qFits
  copies := D.copies
  pre := D.pre
  copiesOK := D.copiesOK
  precOK := D.precOK
  copyFits := D.copyFits
  code := D.code
  codePos := D.codePos
  codeValid := codeFits
  context := D.context
  signedCentre := D.signedCentre
  codeTruth := D.codeTruth

theorem attach_literal_reuses_exact_port_bytes (C : LiteralPortFile T rr cc dd)
    (codeFits : 1+(writeResidents m D.hq (oddAxis m) D.copies D.pre C.raw).result.roster.modes.length<2^D.code) :
    (attachLiteral D C codeFits).source.raw=C.raw := rfl

#print axioms attachLiteral
#print axioms attach_literal_reuses_exact_port_bytes
end
end J6R52FreshExterior
