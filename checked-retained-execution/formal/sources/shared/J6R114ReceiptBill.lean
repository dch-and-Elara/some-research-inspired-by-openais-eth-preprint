import J6R114PrescribedReceipts

/-! Honest accounting for the new receipt family. The per-contraction cost
is that of the receipt consumed by this very fold. -/
namespace J6R114PrescribedReceipts
open scoped Polynomial Classical BigOperators
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
open J6R36SharedGateway J6R19Retained AOracleMachineTimeTape A1R10 A1R12
open J6R34OfficialGateway J6R68AbsolutePrescribed
open J6R33OriginalJ6 J6R25StableCensus J6R22RootReadout J6R11Repack J6OrientedHostEval
open J6R63Active J6R62ActivePrep J6R14ZeroMode


set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 4900
set_option maxHeartbeats 22000000

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw)
variable (frame : Frame f (J6SourcePrecision.printed m base)) (hv : 0<ell)
variable (groups : ActualGroupReceipts (W:=W) D)

theorem one_head_and_each_actual_group_meter_are_charged
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (raw : List Bool) :
    let H := prepareHead W i j
    let R := fun g=>groups i j g H.result rfl
    let E := SiteFrame G ell frame i
    let bills := bill (fun g=>groupOnSite G D.hf frame i j g (R g)) (groupOrder 64)
    let cost := (actualReceiptSlot (W:=W) D frame hv groups i j raw).steps
    H.steps+bills+3 ≤ cost ∧
      cost ≤ H.steps+bills+
        tupleExtra E.words.length ell (exteriorChild G ell i j (0:Fin 64)).prec 64+3 := by
  let H := prepareHead W i j
  let R := fun g=>groups i j g H.result rfl
  let E := SiteFrame G ell frame i
  let read := fun g=>groupOnSite G D.hf frame i j g (R g)
  let done := completedGroups G D.hf frame hv i j R
  have lower : bill read (groupOrder 64)≤done.steps :=
    (prodM_steps E.hp E.sizePos hv read (groupOrder 64)).1
  have upper := (completed_groups_exact G D.hf frame hv i j R).2
  change H.steps+bill read (groupOrder 64)+3≤H.steps+done.steps+3 ∧
    H.steps+done.steps+3≤H.steps+bill read (groupOrder 64)+
      tupleExtra E.words.length ell (exteriorChild G ell i j (0:Fin 64)).prec 64+3
  change done.steps≤bill read (groupOrder 64)+
    tupleExtra E.words.length ell (exteriorChild G ell i j (0:Fin 64)).prec 64 at upper
  exact ⟨by omega, by omega⟩

#print axioms one_head_and_each_actual_group_meter_are_charged
end
end J6R114PrescribedReceipts

