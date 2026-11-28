import J6R116ReadyFromHeldMeter
import J6R116PhysicalRetainedChartImage

/-! Bill the actual R114 operand assembly once, then the remaining
retained inputs on its same physical receipt. This starts after the
admission: the caller already owns its returned descriptor and bank. -/
namespace J6R117HeldPhysicalImage
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R9Recursive J6R50SourceProducer J6R51Online J6R52FreshExterior
open J6R57PublicRequest J6R54PublicFamily J6R22Active
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables J6R28GeneratedRootFrame
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R55CachedLedger J6R56PrintedExponent J6R49Cost J6R16ModeCost J6R10Reachable
open J6R62ActivePrep J6R64Active J6R66Active J6R66.BootPeak J6R57Public
open J6R67UnifiedRate J6R68ActiveInputs J6R68ActiveInputs.Sweep J6R57ScopeFee
open J6R108FinalDriver J6R111KeptOwnerFlow J6R114SelectedOperands
open J6R68RateJoint.RootWords

open J6R75OuterTime J6R14ZeroMode J6R55Public
open J6R102NativeCodeMeter J6R92NativeWidth J6R55TerminalBootJoined J6R55BootBodies
open J6R55TerminalOrigin J6R53OldOwnerRoot J6R54ExteriorOwner J6R54TerminalBoot

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4900
set_option maxHeartbeats 3800000
set_option pp.maxSteps 1100
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
open J6R116ReadyFromHeld J6R114PrescribedReceipts J6R111KeptOwnerFlow
open J6R57PublicRequest J6R54PublicFamily J6R52FreshExterior

variable {I : SharedInputs G ell q rr cc dd prec kp bw}
variable (image : RequestImage W I)
variable (pad : ℕ)
variable (B : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))

/-- Explicit source suppliers, indexed by the original group address.
The actual post-admission site/bank are inputs to both paid producers. -/
structure HeldConfigurationAt
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64) where
  ownerWidth : ℕ
  rate : ℕ
  rootName : SourceVertex P→Word ownerWidth
  gate : Stamp (KeyWidth kp tc tj) prec
  root : RootRoster (P:=P) gate pad rootName
  rootInjective : Function.Injective rootName
  prep : Prepared G.bounds (G.selector ell) (exteriorChild G ell i j g) (literalSite W image.compiled i j g).hf
  readActual : ∀ (A : ResidentAdmissionCarry (W:=W) image.compiled pad)
    (same : A.site=literalSite W image.compiled i j g)
    (b : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)),
    OwnsHeader A.site.header.result b →
      Meter (RawSelectedSources pad gate root A.site
        (preparedAtOtherSource A.site (literalSite W image.compiled i j g) same prep) rate)
  checkRemaining : ∀ R : PublicOperandReceipt (W:=W) image.compiled pad i j g gate root prep rate,
    Meter (RemainingRetainedInputs image.compiled pad i j g gate root rootInjective R)

variable (sync : B.synced)
variable (reserved : ∀ h∈B.headers,h.id.bits.take kp≠image.compiled.mark.bits)
variable (all : ∀ i j g, HeldConfigurationAt image pad i j g)

def useTheActualHeldConfiguration : PhysicalRetainedImagePlan image where
  pad := pad
  prior := B
  sync := sync
  reserved := reserved
  acquire := fun i j g r sameRow a =>
    let C := all i j g
    have returned :
        (submitResidentRowKeepingSite image.compiled image.tables pad B
          (sourceRow (W:=W) image.compiled i j g)).result=some a.payload := by
      rw [←sameRow]
      exact a.result
    prepareReadyFromTheActualReturnedAdmission image.compiled image.tables pad B i j g C.gate C.root
      C.rootInjective sync reserved a.payload C.readActual returned C.checkRemaining
  acquireScale := by
    intro i j g r sameRow a
    let C := all i j g
    have returned :
        (submitResidentRowKeepingSite image.compiled image.tables pad B
          (sourceRow (W:=W) image.compiled i j g)).result=some a.payload := by
      rw [←sameRow]
      exact a.result
    exact the_actual_preparer_returns_source_scale image.compiled image.tables pad B i j g
      C.gate C.root C.rootInjective sync reserved a.payload C.readActual returned C.checkRemaining

#print axioms useTheActualHeldConfiguration
end
end J6R117HeldPhysicalImage

