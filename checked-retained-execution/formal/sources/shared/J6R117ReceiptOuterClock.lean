import J6R114ReceiptBill
import J6R75OuterTimeBounds

/-! The physical group operation is a metered, verified receipt on
the same original point and frame. This interface supports the new
kept-owner continuation without equating its running time to the old
machine. No proof-side group or value is run a second time. -/
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
set_option maxRecDepth 5000
set_option maxHeartbeats 26000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)

variable (frame : Frame f (J6SourcePrecision.printed m base)) (hv : 0<ell)

variable (executeGroups : ActualGroupReceipts (W:=W) D)

open J6R75OuterTime

theorem paid_actual_receipt_site_has_the_clock_of_its_own_slots
    (Q : ℕ)
    (each : ∀ (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)),
      (actualReceiptSlot (W:=W) D frame hv executeGroups i j (S.requests.probes.read j).result.val).steps≤Q)
    (i : J6Recovery.Addr m) :
    (actualReceiptSite (W:=W) D S frame hv executeGroups i).steps ≤
      rootSiteFee f.natDegree m (literalDegree m native) ell (J6SourcePrecision.printed m base) frame.hp+
        (literalDegree m native+1)*Q := by
  let oracle := receiptSpecification (W:=W) D frame hv executeGroups
  have B0 (j : Fin (literalDegree m native+1)) :
      (S.requests.probes.read j).steps≤(literalDegree m native+1)*(f.natDegree+2) := by
    rw [resident_probe_input_has_the_original_tariff D S]
    exact ((build_root_probe_receipt G ell).2 j).2
  have cap := oracle_site_paid G S.requests.probes B0 oracle hv i
  have direct := actual_receipt_site_uses_the_validated_slots (W:=W) D S frame hv executeGroups i
  have slots : ((probeOrder (literalDegree m native+1)).map (fun j=>
      (actualReceiptSlot (W:=W) D frame hv executeGroups i j
        (S.requests.probes.read j).result.val).steps)).sum≤(literalDegree m native+1)*Q := by
    rw [probeOrder,List.map_ofFn,List.sum_ofFn]
    exact (Finset.sum_le_sum (fun j _=>each i j)).trans (le_of_eq (by simp))
  rw [direct.fee]
  exact Nat.add_le_add cap slots

theorem the_guarded_count_has_the_clock_of_the_actual_admitted_receipts
    (Q : ℕ)
    (each : ∀ (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)),
      (actualReceiptSlot (W:=W) D frame hv executeGroups i j (S.requests.probes.read j).result.val).steps≤Q)
    (positiveBase : 0<base) (allZero : coreA P (fun _=>false)=true)
    (answer : ℕ) (count : Nat.card {x : Fin m→Bool // coreA P x=true ∧ coreB P x=true}=1+answer) :
    let out := runActualReceiptCount (W:=W) D S frame hv executeGroups
    let pads := (exactPadOrder m (K m) (printedHalf m) (constantRootWord m)).length
    let site := rootSiteFee f.natDegree m (literalDegree m native) ell (J6SourcePrecision.printed m base) frame.hp+
        (literalDegree m native+1)*Q
    bitsValue out.result.val=answer ∧
      out.steps≤stablePadBudget (a m) (K m) (printedHalf m) (printedRankWidth m)+
        legalRootBudget (J6SourcePrecision.printed m base) (printedFactorWidth m n) (printedAnswerWidth m base)
           ell frame.words.length (printedRankWidth m-a m+13*a m) m pads+8+
            gatheredOracleFee m frame.words.length ell (J6SourcePrecision.printed m base) site := by
  have signed := actual_receipts_give_exact_count_and_each_its_own_cost (W:=W)
    D S frame hv executeGroups positiveBase allZero answer count
  have per := paid_actual_receipt_site_has_the_clock_of_its_own_slots (W:=W) D S frame hv executeGroups Q each
  have hg := gather_site_bill frame m _ (actualReceiptSite (W:=W) D S frame hv executeGroups) per
  exact ⟨signed.1,signed.2.trans (Nat.add_le_add_left hg _)⟩

#print axioms paid_actual_receipt_site_has_the_clock_of_its_own_slots
#print axioms the_guarded_count_has_the_clock_of_the_actual_admitted_receipts
end
end J6R114PrescribedReceipts

