import J6R113SelectedPeakOnImageCore

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

local instance namedGroupDecision :
    DecidableEq (J6R10Reachable.Envelope (N A.sel) (Childs A.sel) Ext) :=
  J6R24MeteredRecursion.sourceDecision A.sel Ext

/-- The named raw provider actually used at this successful row.
The mount equality keeps the exact bill; the provenance of its
internal boot cuts still comes from the literal mounted program. -/
structure CanonicalGroupNames (b : Bank)
    (ack : (submitResidentRow D S pad prior row).result=some (b,true))
    (own : OwnsHeader (Site).header.result b) (rank width : ℕ) where
  beforeStop : OnlineMachine Prep Key prec tw bw Pg rate
  basePos : 0<base
  order : Fin (Ext).edges ≃ (Ext).host.Edge
  provider : OwnerInputProvider (T:=Prep) (pad:=pad) Site
  current : CurrentLayoutSources Prep Key prec tw bw Pg rank (Site).header.result
  fit : ∀ {x : Call (PhysicalHost f ell)} (p : Path A.sel Ext x)
      (a : (printedParams (f:=f) (ell:=ell) s).cutoff<x.edges),
    InputFits A.sel (readyAtPath Prep p a) rate
  bytes : (canonicalTable f.natDegree (Nd+1)).result=OldOrderedBytes f.natDegree Nd Cap
  tails : SavedDirectoryTails width
  layoutWidth : cw=rank+1
  keepSame : cast (congrArg (RetainedAfter Prep Key prec tw bw Pg rate) layoutWidth) A.keep=
    current.retained fit
  layoutSame : cast (congrArg (fun b=>ExteriorLayout (T:=Prep) (page:=Pg) (cw:=b) Site) layoutWidth)
      A.layout = (fun bank header active=>(current.exterior bank header active).run)
  retireSame : A.retire=retireSavedDirectory tails
  chartSame : Q.paidChart=mountFullChart Prep bytes
  chosenSame : (Q.paidChosen b ack own).result=withPaidOwnerLeaves Site beforeStop basePos order provider

#print axioms CanonicalGroupNames
end
end J6R113SelectedPeakOnImage

