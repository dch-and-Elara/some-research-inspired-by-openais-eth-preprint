import J6R75OuterTimeGroup

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 5000
set_option maxHeartbeats 14000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! Specialize the R68 absolute-depth tariff to the same per-row core
that the paid public dispatcher invokes, using actual phase inequalities
on its real occurrence tree. No whole-subcall fee is assumed here. -/
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
open J6R34OfficialGateway J6R33OriginalJ6 J6R68AbsolutePrescribed
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

variable {s C rate cw : ℕ} {cfg : RootBounds s C f}
variable (prior : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
variable (R : RawGroupPlans D S pad prior cfg rate cw)
variable (sync : prior.synced) (reserved : ∀ x∈prior.headers,x.id.bits.take kp≠D.mark.bits)

def actualGroupPhaseCaps
    (i : Centre) (j : Sample) (g : Fin 64) (fixed arithmetic perScope : ℕ) : Prop :=
  let row := sourceRow (W:=W) D i j g
  let A := R i j g
  let X := actualExterior (W:=W) D row
  let E := physicalExteriorInputs X A.layout
  let mounted := publishedBank D S pad prior row
  let owns := published_head_is_the_actual_raw_header D S pad prior row
  CachedThreePhaseCaps (proofDrivers A.machine A.keep A.chart E mounted owns)
    A.retire mounted fixed arithmetic perScope

def uniformRawExteriorRoof (s C scale localPower : ℕ) : ℕ :=
  pathLimit s C*scale*2^((fullPrefixConstant C+localPower)*J9PrintedSchedule.leafThreshold s (Nat.clog 2 s))

theorem the_group_uses_the_actual_absolute_depth_tariff
    (i : Centre) (j : Sample) (g : Fin 64)
    (fixed arithmetic perScope scale localPower : ℕ)
    (caps : actualGroupPhaseCaps D S pad prior R i j g fixed arithmetic perScope)
    (localBound : fixed+(arithmetic+perScope) ≤ scale*2^(localPower*J9PrintedSchedule.leafThreshold s (Nat.clog 2 s))) :
    (coreRawGroup D S pad prior R i j g).steps ≤ uniformRawExteriorRoof s C scale localPower := by
  let row := sourceRow (W:=W) D i j g
  let A := R i j g
  let X := actualExterior (W:=W) D row
  let E := physicalExteriorInputs X A.layout
  let mounted := publishedBank D S pad prior row
  let own := published_head_is_the_actual_raw_header D S pad prior row
  have bound := (actual_raw_sweep_run_from_prescribed_seed A.machine A.keep A.chart E A.retire
    mounted own A.valid A.leaves A.entrance fixed arithmetic perScope scale localPower caps localBound).2.2
  have hdepth : (rawCall (W:=W) D row).depth=1 := rfl
  have hfit : 1 ≤ pathLimit s C := hdepth ▸ A.entrance.depth
  change (coreRawGroup D S pad prior R i j g).steps ≤ (pathLimit s C-(rawCall (W:=W) D row).depth+1)*scale*
      2^((fullPrefixConstant C+localPower)*J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)) at bound
  rw [hdepth,Nat.sub_add_cancel hfit] at bound
  exact bound

#print axioms actualGroupPhaseCaps
#print axioms the_group_uses_the_actual_absolute_depth_tariff
end
end J6R75OuterTime

