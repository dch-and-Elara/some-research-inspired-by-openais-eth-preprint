import J6R117RetainedExteriorClockFold
import J6R116RetainedPrefixArithmetic
import J6R68ActiveInputsSweepRate

/-! Root fixed/arithmetic caps for exactly this held exterior schedule.
The selected layout fee remains a measured, explicit input. -/
namespace J6R117RetainedExteriorClock
open scoped Polynomial Classical BigOperators
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6OrientedHost J6R34RootAtlas
open J6Mesh J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R28GeneratedRootFrame J6R34ChildPath J6R37StructuredRoot J6R41StructuredAllPaths
open J6R54TerminalBoot J6R53OldOwner J6R53OldOwnerRoot J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R52CacheSource
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS J6R10Repack J6ActiveSchedule
open J6R50SourceProducer J6R51Online J6R51ParentFrames J6R52CacheWhole J6R64Active J6R66Active
open J6R59Public J6R94HeldOwnerProvider J6R54PeakInput J6R48RawRoute J6R49SourceLayout
open J6R58RequestSource J6R52Dispatch J6R53Dispatch J6R27OriginalGate J6R36ChildFramedRoute
open J6R62ActivePrep J6R82LayoutDebit V8NativeMessage.N2DLabels J6R68ActiveInputs J6R68ActiveInputs.Sweep
open J6R9Recursive J6R22Active J6R49DFS J6R10Reachable
open J6R111KeptOwnerFlow J6R114RetainedPeak J6R115RetainedPeakPath
open J6R52Peak J6R53PeakAddon J6R55SelectedPeak J6R75RawPeak J6R66.BootPeak J6R16ModeCost
open J6R116RetainedExteriorPeak J6R49Cost J6R57ActiveFee J6R116RetainedPrefix J6R67UnifiedRate
open J6R58ActivePrep J6R48BitCost J6R50Peak

set_option autoImplicit false
set_option warningAsError true
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 6500000
set_option maxRecDepth 4900
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate rank : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (initial : PageBank f ell key prec tw bw (pageKeyWidth m+pad))
variable (boot : FirstSource X M) (E : ExteriorLabels X M boot rank)
variable (on : (printedParams (f:=f) (ell:=ell) s).cutoff<(exteriorChild G ell X.centre X.sample X.group).edges)

local notation "RootCall" => (exteriorChild G ell X.centre X.sample X.group)
local notation "RootPath" => (Path.root : Path sel (exteriorChild G ell X.centre X.sample X.group)
  (exteriorChild G ell X.centre X.sample X.group))

local instance exteriorClockGeometryEdges : Fintype (RootCall).host.Edge := (RootCall).host.finiteEdge

variable (head : OwnsHeader X.header.result initial)
variable (D : KeptDrivers X M rank)



local notation "ScheduleAt" => (exteriorSchedule X M initial boot E on head D)

/-- Actual exterior widths, not widths inferred from a different
post-transition site. -/
structure ExteriorIncomingFits (tc tj prec edgew rank K : ℕ) : Prop where
  precision : prec≤K
  edge : edgew≤K
  depth : 1≤K
  address : externalAddrWidth tc tj 0≤K
  copyWord : rank+1≤K

theorem exterior_schedule_has_actual_physical_fees
    (K layoutCap : ℕ) (Wb : ExteriorIncomingFits tc tj prec edgew rank K)
    (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=rate) (r:=RootCall) K)
    (cs : PrintedCentreScale s C K)
    (layout : (E.setup on).run.steps≤layoutCap)
    (absoluteHigh : absolutePrecision s (RootCall).edges (RootCall).prec+
        (C*s)*(24*2^(Nat.clog 2 s)+4*(Nat.clog 2 s+1))≤K) :
    SweepPhysicalFees ScheduleAt K (layoutCap+4) := by
  let W := E.setup on
  let packed := exteriorPackedAtFirstScope X M boot E on
  let lay : Meter (AtLayout sel (readyAtPath T RootPath on) (rank+1)) :=
    ⟨packed.result.receipt,packed.steps⟩
  let header := readExterior X initial head
  let fit := D.fit RootPath on
  let taper := actual_path_taper T RootPath on
  let J := D.masks
  have exactLay : lay.steps≤layoutCap+4 := by
    change (selectedLayoutAndLabels W).steps≤_
    rw [(one_parent_layout_produces_old_bytes_and_all_retained_labels W).2.2]
    exact Nat.add_le_add_right layout 4
  have shared : header.steps+(2*(rank+1)+4*rate+5)+4≤sharedHeaderAndCopyRoof K := by
    change (readExterior X initial head).steps+_+4≤_
    rw [(paid_actual_exterior_entry X initial head).2.2]
    exact true_header_and_retained_copy_roof Wb.precision Wb.edge Wb.depth
      Wb.address Wb.copyWord ws.modeWord
  have shape := actual_sweep_stock_grid_and_shape_fit (T:=T) RootPath on K cs
  have setup := exact_capture_and_stock_admission (T:=T)
    M.modeWidth fit taper.1 taper.2 J.table (J.covers RootPath on) header lay
    K (layoutCap+4) ((Nat.le_succ _).trans shape.1) shape.2.1 ws.modeWord Wb.edge shape.2.2 shared exactLay
  have t := true_sweep_selected_tapes_and_probes_are_bounded (T:=T) RootPath on M.modeWidth fit
    J.table (J.covers RootPath on) header lay K ws cs Wb.precision Wb.edge
  have frames := original_sweep_frame_dimensions (T:=T) RootPath on M.modeWidth fit J.table
    (J.covers RootPath on) header lay K ws cs absoluteHigh
  exact ⟨frames.2.2.1,setup,t.2.1,t.2.2⟩

/-- One exterior header read, one packed layout and the known printed
arithmetic. No descendant resident remount is charged in this prefix. -/
theorem exterior_active_prefix_uses_captured_geometry
    (K layoutCap : ℕ) (Wb : ExteriorIncomingFits tc tj prec edgew rank K)
    (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=rate) (r:=RootCall) K)
    (cs : PrintedCentreScale s C K)
    (layout : (E.setup on).run.steps≤layoutCap)
    (absoluteHigh : absolutePrecision s (RootCall).edges (RootCall).prec+
        (C*s)*(24*2^(Nat.clog 2 s)+4*(Nat.clog 2 s+1))≤K) :
    let A := ScheduleAt
    A.steps+fixedActive A.result.proofView (reachable_positive T (RootPath).reached) T.vPositive ≤
      sweptSetupPx K (layoutCap+4)+fixedArithmeticPx K (preparedCentrePx K) (mountedMaskPx K) ∧
    ∀ t∈A.result.proofView.centres,
      unitMode (A.result.proofView.tape t).low (A.result.proofView.tape t).tape.result ≤
        64*physicalAddressUnit K := by
  let A := ScheduleAt
  have fields := exterior_schedule_has_actual_physical_fees X M initial boot E on head D K layoutCap
    Wb ws cs layout absoluteHigh
  have fixedCharge := fixed_arithmetic_of_the_actual_retained_descriptor RootPath on A.result.proofView K
    (preparedCentrePx K) (mountedMaskPx K) ws cs fields.high fields.tape fields.mask
  exact ⟨Nat.add_le_add fields.setup fixedCharge, fun t _=>
    unit_tariff_of_the_actual_retained_descriptor RootPath on A.result.proofView K ws t⟩

#print axioms exterior_schedule_has_actual_physical_fees
#print axioms exterior_active_prefix_uses_captured_geometry
end
end J6R117RetainedExteriorClock
