import J6R75OuterTimeCount

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

/-- The same evaluated query head is shared by the actual 64 local
groups. The encoded contract is part of the receipt type. -/
abbrev ActualGroupReceipts :=
  ∀ (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)
    (H : ExactHead m native tc tj tw i j), H=(prepareHead W i j).result →
      GroupReceipt (ell:=ell) G D.hf i j g

variable (executeGroups : ActualGroupReceipts (W:=W) D)

def actualReceiptSlot : SlotProgram (ell:=ell) (F:=frame) G :=
  fun i j _ =>
    let H := prepareHead W i j
    let product := completedGroups G D.hf frame hv i j
      (fun g=>executeGroups i j g H.result rfl)
    ⟨product.result,H.steps+product.steps+3⟩

/-- Only used in the proof of the paid interpolation's semantics. -/
def receiptSpecification : CompletedOracle G ell frame D.hf :=
  completedOracle G D.hf frame hv
    (fun i j g=>executeGroups i j g (prepareHead W i j).result rfl)

theorem the_paid_receipt_slot_is_correct_at_its_actual_probe
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (raw : List Bool)
    (good : raw=List.ofFn ((rootPreset G ell).word j)) :
    (actualReceiptSlot (W:=W) D frame hv executeGroups i j raw).result=
      (receiptSpecification (W:=W) D frame hv executeGroups).reply i j raw :=
  (gateway_reply_exact G D.hf frame hv
    (fun a b g=>executeGroups a b g (prepareHead W a b).result rfl) i j raw good).1.symm

def actualReceiptSite (i : J6Recovery.Addr m) : Meter (Block frame ell) :=
  paidSite G S.requests.probes (actualReceiptSlot (W:=W) D frame hv executeGroups) D.hf hv i

theorem actual_receipt_site_uses_the_validated_slots (i : J6Recovery.Addr m) :
    Delta (actualReceiptSite (W:=W) D S frame hv executeGroups i)
      (oracleSite G S.requests.probes (receiptSpecification (W:=W) D frame hv executeGroups) hv i)
      ((probeOrder (literalDegree m native+1)).map (fun j=>
        (actualReceiptSlot (W:=W) D frame hv executeGroups i j (S.requests.probes.read j).result.val).steps)).sum :=
  actual_paid_site_delta G S.requests.probes (actualReceiptSlot (W:=W) D frame hv executeGroups)
    (receiptSpecification (W:=W) D frame hv executeGroups)
    (the_paid_receipt_slot_is_correct_at_its_actual_probe (W:=W) D frame hv executeGroups) hv i

def runActualReceiptCount : Meter (A1R10.Word (printedAnswerWidth m base)) :=
  let fit := printed_readout_fits m n base (constantRootWord m)
  countFromMeasuredSlots frame fit.1 fit.2.1 m (printedHalf m) n (printedRankWidth m)
    (J6R14LayoutCost.wordCell (J6RecursiveOrientation.diagonal (constantRootWord m)))
    (actualReceiptSite (W:=W) D S frame hv executeGroups)

theorem actual_receipts_give_exact_count_and_each_its_own_cost
    (positiveBase : 0<base) (allZero : coreA P (fun _=>false)=true)
    (answer : ℕ) (count : Nat.card {x : Fin m→Bool // coreA P x=true ∧ coreB P x=true}=1+answer) :
    let sites := actualReceiptSite (W:=W) D S frame hv executeGroups
    let out := runActualReceiptCount (W:=W) D S frame hv executeGroups
    let pads := (exactPadOrder m (K m) (printedHalf m) (constantRootWord m)).length
    bitsValue out.result.val=answer ∧
      out.steps≤stablePadBudget (a m) (K m) (printedHalf m) (printedRankWidth m)+
        legalRootBudget (J6SourcePrecision.printed m base) (printedFactorWidth m n) (printedAnswerWidth m base)
          ell frame.words.length (printedRankWidth m-a m+13*a m) m pads+8+gatherCost frame m sites := by
  let sites := actualReceiptSite (W:=W) D S frame hv executeGroups
  let slots (i : J6Recovery.Addr m) := (slotRead frame m sites i).result
  let fit := printed_readout_fits m n base (constantRootWord m)
  let O := receiptSpecification (W:=W) D frame hv executeGroups
  have hF : 0<f.natDegree := frame.natDegree D.hf ▸ frame.sizePos
  have truth (i : J6Recovery.Addr m) :
      frame.decode (slots i)=
        (polynomial
          (stableRootPacking m (printedHalf m) n (printedRankWidth m) P (constantRootWord m)
            G.room G.half G.rankA G.rankFit.le)
          (oddAxis m) (index m i:ℤ) (J6SourcePrecision.printed m base)
          (rootEntryFile f ell base P (constantRootWord m)) D.hf).eval 0 := by
    change frame.decode (slotRead frame m sites i).result=_
    rw [(stored_slot_exact frame m sites i).1]
    have exactSite := actual_receipt_site_uses_the_validated_slots (W:=W) D S frame hv executeGroups i
    change frame.decode (sites i).result=_
    rw [exactSite.value]
    exact (oracle_site_exact G S.requests.probes O hv i).1
  have signed := compact_stable_native_words m n base base (printedHalf m) (printedFactorWidth m n)
    (printedAnswerWidth m base) (printedRankWidth m) P (constantRootWord m) allZero answer
    (J6R52PublicSlot.actual_outer_at_one_guarded_count m n P answer count)
    G.room G.half (printed_rank_width m).1 G.rankA G.rankFit D.hf positiveBase hF hv
    frame.hp fit.1 fit.2.1 frame.exactMod slots
    (fun i=>by
      have h := truth i
      change boxTransport frame.exactMod (uvRead frame.hp frame.words ell (slots i))=_ at h
      simpa only [boxTransport_cast] using h)
    fit.2.2.1 fit.2.2.2
  have E := metered_slot_append frame fit.1 fit.2.1 m (printedHalf m) n (printedRankWidth m)
    (J6R14LayoutCost.wordCell (J6RecursiveOrientation.diagonal (constantRootWord m))) sites
  refine ⟨(congrArg (fun w : A1R10.Word (printedAnswerWidth m base)=>bitsValue w.val) E.1).trans signed.1,?_⟩
  exact E.2.trans (Nat.add_le_add_right signed.2 _)

#print axioms the_paid_receipt_slot_is_correct_at_its_actual_probe
#print axioms actual_receipt_site_uses_the_validated_slots
#print axioms actual_receipts_give_exact_count_and_each_its_own_cost
end
end J6R114PrescribedReceipts
