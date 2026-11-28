import J6R111KeptOwnerFlowRun
import J6R68ActiveInputsSweepRate

/-! Numerical fields on the actual R111 retained R68 schedule. The
preparation is the real incoming header and the retained layout once. -/
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

open J6R111KeptOwnerFlow J6R57ActiveFee J6R67UnifiedRate J6R58LeafScale J6R50Peak
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

structure RetainedIncomingFits (K : ℕ) : Prop where
  precisionWord : prec≤K
  edgeWord : x.site.birth.edge≤K
  depthWord : x.site.birth.dep≤K
  headerPrefix : x.site.birth.job.offset≤K
  copyWord : rank+1≤K

/-- Only a name for the actual active call's schedule. -/
abbrev actualRetainedSchedule
    (on : (printedParams (f:=f) (ell:=ell) s).cutoff<x.call.edges) :
    Meter (Schedule sel (readyAtPath T (.step x.path x.slot) on) T.bank rate) :=
  let path := Path.step x.path x.slot
  let H := readGroupHeadersForActive X x.path x.slot x.site x.entry
  let W := D.layout x on H.result
  let L := selectedLayoutAndLabels W.setup
  prepareFromKeptLayout X x.path x.slot x.site x.entry M on L.result
    (D.fit path on) D.masks L.steps

theorem actual_retained_schedule_has_its_own_physical_tariffs
    (on : (printedParams (f:=f) (ell:=ell) s).cutoff<x.call.edges)
    (K layoutCap : ℕ) (Wb : RetainedIncomingFits X M (rank:=rank) x K)
    (ws : ActiveWidthScale (ell:=ell) (s:=s) (C:=C) (q:=rate)
      (r:=exteriorChild G ell X.centre X.sample X.group) K)
    (cs : PrintedCentreScale s C K)
    (layout : let H := readGroupHeadersForActive X x.path x.slot x.site x.entry
      (D.layout x on H.result).setup.run.steps≤layoutCap)
    (absoluteHigh : absolutePrecision s (exteriorChild G ell X.centre X.sample X.group).edges
        (exteriorChild G ell X.centre X.sample X.group).prec+
      (C*s)*(24*2^(Nat.clog 2 s)+4*(Nat.clog 2 s+1)) ≤ K) :
    SweepPhysicalFees (actualRetainedSchedule X M D x on) K (layoutCap+4) := by
  let path := Path.step x.path x.slot
  let H := readGroupHeadersForActive X x.path x.slot x.site x.entry
  let W := D.layout x on H.result
  let L := selectedLayoutAndLabels W.setup
  let lay : Meter (AtLayout sel (readyAtPath T path on) (rank+1)) := ⟨L.result.receipt,L.steps⟩
  let header := readIncoming x.site x.entry.bank x.entry.own
  let J := D.masks
  let fit := D.fit path on
  let taper := actual_path_taper T path on
  let current := prepare (bank:=T.bank) M.modeWidth fit taper.1 taper.2 X.hf
    J.table (J.covers path on) header lay
  have exactLay : lay.steps≤layoutCap+4 := by
    change L.steps≤_
    rw [(one_parent_layout_produces_old_bytes_and_all_retained_labels W.setup).2.2]
    exact Nat.add_le_add_right layout 4
  have shared : header.steps+(2*(rank+1)+4*rate+5)+4≤sharedHeaderAndCopyRoof K := by
    change (readIncoming x.site x.entry.bank x.entry.own).steps+_+4≤_
    rw [(incoming_words_from_published_head x.site x.entry.bank x.entry.own).2.2]
    exact true_header_and_retained_copy_roof Wb.precisionWord Wb.edgeWord Wb.depthWord
      Wb.headerPrefix Wb.copyWord ws.modeWord
  have shape := actual_sweep_stock_grid_and_shape_fit (T:=T) path on K cs
  have prep := exact_capture_and_stock_admission (T:=T)
    M.modeWidth fit taper.1 taper.2 J.table (J.covers path on) header lay
    K (layoutCap+4) ((Nat.le_succ _).trans shape.1) shape.2.1 ws.modeWord Wb.edgeWord shape.2.2 shared exactLay
  have t := true_sweep_selected_tapes_and_probes_are_bounded (T:=T) path on M.modeWidth fit
    J.table (J.covers path on) header lay K ws cs Wb.precisionWord Wb.edgeWord
  have frames := original_sweep_frame_dimensions (T:=T) path on M.modeWidth fit J.table
    (J.covers path on) header lay K ws cs absoluteHigh
  change SweepPhysicalFees current K (layoutCap+4)
  exact ⟨frames.2.2.1,prep,t.2.1,t.2.2⟩

#print axioms actualRetainedSchedule
#print axioms actual_retained_schedule_has_its_own_physical_tariffs
end
end J6R116RetainedPrefix
