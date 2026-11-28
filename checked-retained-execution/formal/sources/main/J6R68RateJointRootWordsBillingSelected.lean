import J6R68RateJointRootWordsBillingAttach
import J6R68RateJointRootWordsOnlineProgram
import J6R68RateJointRootWordsBillingTop

/-! Concrete first-ingress factory: the real selected source provider
is used by construction, not assumed equal to the old callback meter.
No other original R66 field is modified. -/
namespace J6R68RateJoint.RootWords
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6Mesh J6OrientedHost J6R24LegalLayout J6R31RootResidentTables
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R35RootOrigins
open J6R26DescriptorTree J6R33StatefulArithmeticPage J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R55BootBodies J6R30ProducedGateRegistry J6R55TerminalBootJoined
open J6R24MeteredRecursion J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun
open J6R51Online J6R32StatefulArithmetic J6R48RawRoute
open J6R54ExteriorOwner J6R55TerminalOrigin J6R53OldOwnerRoot J6R50SourceProducer
open J6R67UnifiedRate

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4200
set_option maxHeartbeats 7000000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section
attribute [local irreducible] J6R12Blueprint.printedParams

variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw own rate : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable (gate : Stamp key prec) (pad : ℕ)
variable {s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (L : BootLaneTape X gate pad)
variable (make : ∀ w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group),
  Meter (FirstSlotBook (r:=exteriorChild G ell X.centre X.sample X.group) (sel:=sel) T key prec tw bw (pageKeyWidth m+pad) w))
variable (order : ∀ w : (Plan sel).Slot (exteriorChild G ell X.centre X.sample X.group),
  (make w).result.datum.geometry.edges=orderedExteriorEdges X)
variable {rootName : SourceVertex P→Word own}
variable (root : RootRoster (P:=P) gate pad rootName)
variable (D : OwnerWordsAtBodies X gate pad root (firstBodiesFromSelectedHandles X gate pad L make order))
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable (B : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (live : IsLive (X.seed pad) B) (inj : Function.Injective rootName)
local notation "A" => (firstBodiesFromSelectedHandles X gate pad L make order)
local notation "Y" => (withJoinedBoot X gate pad root M A D B live inj)

def ingressForPaidFirstSelector : ActualFirstIngress Y :=
  ingressOfActualJoinedMachine X gate pad A make
    (firstBodiesFromSelectedHandles_uses_exact_paid_operation X gate pad L make order) root D M B live inj

def measuredScopeFromPaidFirstSelector (rest : RemainingScopeInputs Y B)
    (sizes : ActualIngressDimensions Y (ingressForPaidFirstSelector X gate pad L make order root D M B live inj))
    (pos : 0 < key) (room : X.issue.result.val+1 < 2^key) : MeasuredScopeInputs Y B :=
  scopeWithMeasuredIngress rest (ingressForPaidFirstSelector X gate pad L make order root D M B live inj)
    sizes pos room

#print axioms ingressForPaidFirstSelector
#print axioms measuredScopeFromPaidFirstSelector
end
end J6R68RateJoint.RootWords

