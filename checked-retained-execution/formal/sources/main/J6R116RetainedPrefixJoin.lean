import J6R116RetainedPrefixArithmetic
import J6R116RetainedPrefixFields
import J6R116RetainedPrefixOperands

/-! The actual one-read, one-layout descendant prefix, together with
the real per-mode unit cost. Both are on the installed retained run. -/
namespace J6R116RetainedPrefix
open scoped Classical Polynomial BigOperators
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6OrientedHost J6R34RootAtlas
open J6Mesh J6R24LegalLayout J6R26StablePreparedRoot J6R27PrescribedProbe J6R31RootResidentTables
open J6R32RootGeneratedRegistryInputs J6R34ChildPath J6R37StructuredRoot J6R41StructuredAllPaths
open J6R54TerminalBoot J6R53OldOwner J6R53OldOwnerRoot J6R26DescriptorTree J6R30ProducedGateRegistry
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R24MeteredRecursion J6R52CacheSource
open J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R48DFS J6R10Repack J6ActiveSchedule
open J6R50SourceProducer J6R51Online J6R51ParentFrames J6R52CacheWhole J6R64Active J6R66Active
open J6R59Public J6R94HeldOwnerProvider J6R54PeakInput J6R48RawRoute J6R49SourceLayout
open J6R58RequestSource J6R52Dispatch J6R53Dispatch J6R27OriginalGate J6R36ChildFramedRoute
open J6R62ActivePrep J6R82LayoutDebit V8NativeMessage.N2DLabels J6R68ActiveInputs J6R68ActiveInputs.Sweep
open J6R9Recursive J6R22Active J6R49DFS J6R10Reachable J6R49Leaf J6R57Public J6R49Cost

open J6R21Leaf J6R111KeptOwnerFlow J6R57ActiveFee J6R67UnifiedRate J6R58LeafScale J6R50Peak
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 39000000
set_option maxRecDepth 5600
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ}
variable {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P
  (J6R28GeneratedRootFrame.constantRootWord m)}
variable {ell q ro co de edgew tc tj key prec tw bw : ℕ}
variable (X : StableExterior G ell q ro co de edgew tc tj key prec tw bw)
variable {pad s C rate rank : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {T : Prepared cfg sel (exteriorChild G ell X.centre X.sample X.group) X.hf}
variable (M : OnlineMachine T key prec tw bw (pageKeyWidth m+pad) rate)
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : KeptDrivers X M rank)
variable (x : KeptInvocation X M)


theorem actual_retained_active_prefix_has_fixed_and_unit_caps
    (on : (printedParams (f:=f) (ell:=ell) s).cutoff<x.call.edges)
    (K layoutCap : ℕ) (Wb : RetainedIncomingFits X M (rank:=rank) x K)
    (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=rate)
      (r:=exteriorChild G ell X.centre X.sample X.group) K)
    (cs : PrintedCentreScale s C K)
    (geo : LocalOwnerGeometry X x.path x.slot x.site K)
    (layout : let H := readGroupHeadersForActive X x.path x.slot x.site x.entry
      (D.layout x on H.result).setup.run.steps≤layoutCap)
    (absoluteHigh : absolutePrecision s (exteriorChild G ell X.centre X.sample X.group).edges
        (exteriorChild G ell X.centre X.sample X.group).prec+
      (C*s)*(24*2^(Nat.clog 2 s)+4*(Nat.clog 2 s+1)) ≤ K) :
    let path := Path.step x.path x.slot
    let H := readGroupHeadersForActive X x.path x.slot x.site x.entry
    let A := actualRetainedSchedule X M D x on
    let hp := reachable_positive T path.reached
    H.steps+(mountResident x.site x.entry.resident).steps+A.steps+
      fixedActive A.result.proofView hp T.vPositive≤
      groupHeadScanRoof K (vertexCount (exteriorChild G ell X.centre X.sample X.group).host+4*(C*s))+
        sweptActivePx K (layoutCap+4) ∧
    ∀ t∈A.result.proofView.centres,
      unitMode (A.result.proofView.tape t).low (A.result.proofView.tape t).tape.result≤64*physicalAddressUnit K := by
  let path := Path.step x.path x.slot
  let H := readGroupHeadersForActive X x.path x.slot x.site x.entry
  let A := actualRetainedSchedule X M D x on
  have fees := actual_retained_schedule_has_its_own_physical_tariffs X M D x on K layoutCap
    Wb ws cs layout absoluteHigh
  have f := fixed_arithmetic_of_the_actual_retained_descriptor path on A.result.proofView
    K (preparedCentrePx K) (mountedMaskPx K) ws cs fees.high fees.tape fees.mask
  have h := actual_retained_parent_headers_pay_one_true_roster_scan X M x K geo
  have r := actual_retained_resident_mount_has_its_real_word_roof X M x K geo
  have setup := fees.setup
  refine ⟨?_, fun t _=>unit_tariff_of_the_actual_retained_descriptor path on A.result.proofView K ws t⟩
  unfold sweptActivePx activeNodeFixedPrice
  simpa only [Nat.add_assoc] using Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h r) setup) f

#print axioms actual_retained_active_prefix_has_fixed_and_unit_caps
end
end J6R116RetainedPrefix
