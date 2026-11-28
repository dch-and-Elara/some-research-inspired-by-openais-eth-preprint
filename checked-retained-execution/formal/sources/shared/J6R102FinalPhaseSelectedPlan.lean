import J6R102FinalPhaseProfile
import J6R75OuterTimeFinal

/-! Bind the numeric source recipe to each actual numbered group in
R75. The recorded equalities are identities of the selected program
components, not equal responses or fee bounds borrowed from another
execution. In a driver constructed from these components they are rfl. -/
namespace J6R102FinalPhase
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
open J6R64Active J6R66Active J6R66.BootPeak J6R57Public
open J6R67UnifiedRate J6R68ActiveInputs J6R68ActiveInputs.Sweep J6R57ScopeFee
open J6R75OuterTime J6R79Numeric J6R14ZeroMode

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4900
set_option maxHeartbeats 22000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
variable (pad : ℕ)
variable (prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
variable {s C rate rank : ℕ} {cfg : RootBounds s C f}
variable (row : Entry D.mark m native tc tj tw)
variable (A : RawGroupPlan D S pad prior row cfg rate (rank+1))
local notation "X" => (actualExterior (W:=W) D row)
local notation "B0" => (publishedBank D S pad prior row)
local notation "Owns" => (published_head_is_the_actual_raw_header D S pad prior row)

structure SelectedPlanSource (K producerPower leafPower : ℕ) (coefficients : ProducerCoefficients) where
  beforeStop : OnlineMachine A.prep (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad) rate
  basePos : 0<base
  edgeOrder : Fin (rawCall (W:=W) D row).edges ≃ (rawCall (W:=W) D row).host.Edge
  stopSource : OwnerInputProvider (T:=A.prep) (pad:=pad) (actualExterior (W:=W) D row)
  recipe : MeasuredProfile (T:=A.prep) (rank:=rank) (actualExterior (W:=W) D row) beforeStop
    basePos edgeOrder stopSource (publishedBank D S pad prior row) (published_head_is_the_actual_raw_header D S pad prior row)
    K producerPower leafPower coefficients
  machine : A.machine=withPaidOwnerLeaves (actualExterior (W:=W) D row) beforeStop basePos edgeOrder stopSource
  keep : A.keep=recipe.current.retained recipe.fit
  chart : A.chart=recipe.chart
  exterior : A.layout=(fun b own level=>(recipe.current.exterior b own level).run)
  retire : A.retire=retireSavedDirectory recipe.tails

theorem selected_plan_has_the_derived_clock
    (K producerPower leafPower : ℕ) (coefficients : ProducerCoefficients)
    (T0 : SelectedPlanSource D S pad prior row A K producerPower leafPower coefficients) :
    let L := localClock s K producerPower leafPower coefficients
    CachedThreePhaseCaps
      (proofDrivers A.machine A.keep A.chart (physicalExteriorInputs X A.layout) B0 Owns)
      A.retire B0 L L L := by
  dsimp only
  rw [T0.machine,T0.keep,T0.chart,T0.exterior,T0.retire]
  exact measured_profile_caps_the_given_source X T0.beforeStop T0.basePos T0.edgeOrder T0.stopSource
    B0 Owns K producerPower leafPower coefficients T0.recipe

#print axioms SelectedPlanSource
#print axioms selected_plan_has_the_derived_clock
end
end J6R102FinalPhase

