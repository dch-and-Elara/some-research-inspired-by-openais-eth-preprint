import J6R75OuterTimeAdmit
import J6R33OriginalJ6Oracle
import J6R68ActiveInputsSweepLedger

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 5000
set_option maxHeartbeats 14000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! One actual paid head is re-used by its 64 group emissions. Each
operand then uses original R57 submit on the actual incoming bank and the
very same R68 contraction. No lookup or sample check is replaced by proof. -/
namespace J6R75OuterTime
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R35RootOrigins J6R26DescriptorTree J6R34ChildPath J6R35GatewayPreparation
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R30ProducedGateRegistry
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS
open J6R9Recursive J6R50SourceProducer J6R51Online J6R52FreshExterior
open J6R57PublicRequest J6R54PublicFamily J6R22Active
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables J6R28GeneratedRootFrame
open J6R32RootGeneratedRegistryInputs J6R37StructuredRoot J6R41StructuredAllPaths
open J6R55CachedLedger J6R56PrintedExponent J6R49Cost J6R16ModeCost J6R10Reachable
open J6R64Active J6R66Active J6R66.BootPeak
open J6R67UnifiedRate J6R68ActiveInputs J6R68ActiveInputs.Sweep
open J6R19Retained AOracleMachineTimeTape A1R10 A1R12
open J6R68AbsolutePrescribed
open J6R63Active J6R62ActivePrep J6R14ZeroMode

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
variable (pad : ℕ)
local notation "Centre" => (J6Recovery.Addr m)
local notation "Sample" => (Fin (literalDegree m native+1))

abbrev sourceRow (i : Centre) (j : Sample) (g : Fin 64) : Entry D.mark m native tc tj tw :=
  (emitAt W D.mark ((i,j),g)).result

theorem canonical_source_row_is_resident (i : Centre) (j : Sample) (g : Fin 64) :
    sourceRow (W:=W) D i j g∈S.requests.rows := by
  rw [S.requests.ordered]
  exact every_public_address_is_stored W D.mark ((i,j),g)

variable {s C : ℕ}

/-- Selected physical drivers, not scalar answers or caps on whole slots. -/
structure RawGroupPlan
    (prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
    (row : Entry D.mark m native tc tj tw) (cfg : RootBounds s C f) (rate cw : ℕ) where
  sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)
  prep : Prepared cfg sel (rawCall (W:=W) D row) (actualExterior (W:=W) D row).hf
  machine : OnlineMachine prep (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate
  keep : RetainedAfter prep (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate cw
  chart : MountedChart prep
  layout : ExteriorLayout (T:=prep) (page:=pageKeyWidth m+pad) (cw:=cw) (actualExterior (W:=W) D row)
  retire : PageJob f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)→ℕ
  valid : ReadyOnStack (borns machine) (publishedBank D S pad prior row)
  leaves : letI : DecidableEq (J6R10Reachable.Envelope (N sel) (Childs sel) (rawCall (W:=W) D row)) :=
    J6R24MeteredRecursion.sourceDecision sel (rawCall (W:=W) D row)
    LeafAgreement machine (publishedBank D S pad prior row)
  entrance : AbsoluteSeed s C (rawCall (W:=W) D row)

abbrev RawGroupPlans
    (prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
    (cfg : RootBounds s C f) (rate cw : ℕ) :=
  ∀ (i : Centre) (j : Sample) (g : Fin 64),
    RawGroupPlan D S pad prior (sourceRow (W:=W) D i j g) cfg rate cw

variable {cfg : RootBounds s C f} {rate cw : ℕ}
variable (prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))

abbrev frameOfPlan (row : Entry D.mark m native tc tj tw)
    (A : RawGroupPlan D S pad prior row cfg rate cw) : Frame f (rawCall (W:=W) D row).prec :=
  A.prep.frame (Path.root : Path A.sel (rawCall (W:=W) D row) (rawCall (W:=W) D row)).reached

abbrev actualGroupFrame (R : RawGroupPlans D S pad prior cfg rate cw)
    (i : Centre) (j : Sample) (g : Fin 64) : Frame f (exteriorChild G ell i j g).prec :=
  frameOfPlan D S pad prior (sourceRow (W:=W) D i j g) (R i j g)

#print axioms canonical_source_row_is_resident
#print axioms RawGroupPlan
#print axioms frameOfPlan
#print axioms actualGroupFrame
end
end J6R75OuterTime

