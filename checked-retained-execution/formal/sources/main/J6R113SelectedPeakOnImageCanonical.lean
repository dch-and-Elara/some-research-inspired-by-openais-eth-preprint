import J6R113SelectedPeakOnImageNames

/-! The exact operands at one genuinely accepted row. These equations
identify callbacks and layout operands, not outputs. This is separate
from using the original R110 named-pause theorem. -/
namespace J6R113SelectedPeakOnImage
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Leaf J6OrientedHost
open J6Mesh J6R34RootAtlas J6R34ChildPath J6R24MeteredRecursion
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R50SourceProducer
open J6R51Online J6R52FreshExterior J6R57PublicRequest J6R54PublicFamily
open J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe
open J6R28GeneratedRootFrame J6R14ZeroMode J6R34OfficialGateway
open J6R68ActiveInputs.Sweep J6R75OuterTime J6R19Retained J1PPrinted
open J6R31RootResidentTables J6R111SelectedGroup J6R108FinalDriver
open J6R110CanonicalCoverage J6R110CanonicalMount J6R109CanonicalProbeTable
open J6R12Blueprint J6ActiveRun J6R9Recursive J6R10Reachable J6R11Blueprint
open J6R57Public J6R68ActiveInputs J6R64Active J6R57ScopeFee J6R66Active J6R62ActivePrep

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4900
set_option maxHeartbeats 7000000
set_option maxSynthPendingDepth 9
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
variable (pad : ℕ) (prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
variable (row : Entry D.mark m native tc tj tw)
variable {s C rate cw : ℕ} {cfg : RootBounds s C f}
variable (A : RawGroupPlan D S pad prior row cfg rate cw)
variable (Q : PaidSetupForPlan D S pad prior row A)
local notation "Site" => (actualExterior (W:=W) D row)
local notation "Ext" => (rawCall (W:=W) D row)
local notation "Prep" => A.prep
local notation "Key" => (KeyWidth kp tc tj)
local notation "Pg" => (pageKeyWidth m+pad)
local notation "Nd" => (fullProbeDegree f.natDegree)
local notation "Cap" => (full_probe_fit f.natDegree)
local notation "Bank" => (PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))

local instance namedGroupExecutionDecision :
    DecidableEq (J6R10Reachable.Envelope (N A.sel) (Childs A.sel) Ext) :=
  J6R24MeteredRecursion.sourceDecision A.sel Ext

private theorem same_literal_reindex {a b : ℕ} (eq : a=b)
    (M : OnlineMachine Prep Key prec tw bw Pg rate)
    (F : RetainedAfter Prep Key prec tw bw Pg rate a)
    (chart : MountedChart Prep) (L : ExteriorLayout (T:=Prep) (page:=Pg) (cw:=a) Site)
    (retire : PageJob f ell Key prec tw bw Pg→ℕ) (bank : Bank) (own : OwnsHeader (Site).header.result bank) :
    runRawPhysicalExterior Site M F chart L retire bank own =
      runRawPhysicalExterior Site M
        (cast (congrArg (RetainedAfter Prep Key prec tw bw Pg rate) eq) F) chart
        (cast (congrArg (fun w=>ExteriorLayout (T:=Prep) (page:=Pg) (cw:=w) Site) eq) L)
        retire bank own := by
  subst b
  rfl

variable {b : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad)}
variable {ack : (submitResidentRow D S pad prior row).result=some (b,true)}
variable {own : OwnsHeader (actualExterior (W:=W) D row).header.result b}
variable {rank width : ℕ}
variable (names : CanonicalGroupNames D S pad prior row A Q b ack own rank width)

/-- The corresponding R110 code, with the chart producer still inside
the invocation. This identified part excludes the chooser's scratch. -/
def canonicalPartOnAcceptedRow :=
  runRawExteriorWithPaidCanonicalChart Site Nd Cap names.bytes
    (canonical_mount_coverage_from_original_prepared Prep)
    (withPaidOwnerLeaves Site names.beforeStop names.basePos names.order names.provider)
    (names.current.retained names.fit)
    (fun bank header active=>(names.current.exterior bank header active).run)
    (retireSavedDirectory names.tails) b own

/-- The R111 acknowledgement split at the selected row's exact provider,
layout and chart. No equality of unrelated count results is used. -/
theorem same_ack_consumes_the_one_named_canonical_part :
    let paid := Q.paidChosen b ack own
    let exactPart := canonicalPartOnAcceptedRow D S pad prior row A Q names
    continueSelectedPublicGroup D S pad prior row Site Q.paidChosen A.keep Q.paidChart A.layout A.retire
      b ⟨ack,own⟩=⟨exactPart.result,paid.steps+exactPart.steps⟩ := by
  let paid := Q.paidChosen b ack own
  let chart := mountFullChart Prep names.bytes
  let selected := withPaidOwnerLeaves Site names.beforeStop names.basePos names.order names.provider
  let L : ExteriorLayout (T:=Prep) (page:=Pg) (cw:=rank+1) Site :=
    fun bank header active=>(names.current.exterior bank header active).run
  let retire : PageJob f ell Key prec tw bw Pg→ℕ := retireSavedDirectory names.tails
  let native := runRawPhysicalExterior Site selected (names.current.retained names.fit) chart.result L retire b own
  let old := runRawPhysicalExterior Site paid.result A.keep Q.paidChart.result A.layout A.retire b own
  have choose : paid.result=selected := names.chosenSame
  have mount : Q.paidChart=chart := names.chartSame
  have discard : A.retire=retire := names.retireSame
  have same : old=native := by
    calc
      old=runRawPhysicalExterior Site selected A.keep chart.result A.layout retire b own := by
        change runRawPhysicalExterior Site paid.result A.keep Q.paidChart.result A.layout A.retire b own=_
        rw [choose,mount,discard]
      _=runRawPhysicalExterior Site selected
          (cast (congrArg (RetainedAfter Prep Key prec tw bw Pg rate) names.layoutWidth) A.keep)
          chart.result
          (cast (congrArg (fun w=>ExteriorLayout (T:=Prep) (page:=Pg) (cw:=w) Site) names.layoutWidth)
            A.layout) retire b own :=
        same_literal_reindex D S pad prior row A names.layoutWidth selected A.keep chart.result A.layout retire b own
      _=native := by rw [names.keepSame,names.layoutSame]
  change (⟨old.result,paid.steps+Q.paidChart.steps+old.steps+3⟩ : Meter _) =
    ⟨native.result,paid.steps+(chart.steps+native.steps+3)⟩
  rw [same,mount]
  exact congrArg (Meter.mk native.result) (by omega)

#print axioms canonicalPartOnAcceptedRow
#print axioms same_ack_consumes_the_one_named_canonical_part
end
end J6R113SelectedPeakOnImage

