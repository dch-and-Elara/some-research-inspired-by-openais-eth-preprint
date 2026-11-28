import J6R75OuterTimeSite
import J6R52PublicSlotOrigin
import J6R57PublicRequestImage
import J6R33OriginalJ6Count
import J6R25StableCensusCompactCompute

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 5000
set_option maxHeartbeats 26000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! Use the original paid public interpolation and signed integer extraction
on the actual R57-wrapped R68 contraction runs. The analogue CompletedOracle
is proof-only; the executable retains the already installed R57 probe bank. -/
namespace J6R75OuterTime
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

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (D : Compiled G ell q rr cc dd prec kp bw) (S : InstalledRequestInputs W D)
variable (pad : ℕ)
variable (B : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))


local notation "Centre" => (J6Recovery.Addr m)
local notation "Sample" => (Fin (literalDegree m native+1))


variable {s C rate cw : ℕ} {cfg : RootBounds s C f}
variable (R : RawGroupPlans D S pad B cfg rate cw)
variable (sync : B.synced) (reserved : ∀ x∈B.headers,x.id.bits.take kp≠D.mark.bits)
variable (frame : Frame f (J6SourcePrecision.printed m base))
variable (hv : 0<ell)

def runRawOuterCount : Meter (A1R10.Word (printedAnswerWidth m base)) :=
  let fit := printed_readout_fits m n base (constantRootWord m)
  countFromMeasuredSlots frame fit.1 fit.2.1 m (printedHalf m) n (printedRankWidth m)
    (J6R14LayoutCost.wordCell (J6RecursiveOrientation.diagonal (constantRootWord m)))
    (rawOuterSite D S pad B R sync reserved frame hv)

theorem exact_guarded_count_from_the_actual_outer_runs
    (positiveBase : 0<base) (allZero : coreA P (fun _=>false)=true)
    (answer : ℕ) (count : Nat.card {x : Fin m→Bool // coreA P x=true ∧ coreB P x=true}=1+answer) :
    let sites := rawOuterSite D S pad B R sync reserved frame hv
    let out := runRawOuterCount D S pad B R sync reserved frame hv
    let pads := (exactPadOrder m (K m) (printedHalf m) (constantRootWord m)).length
    bitsValue out.result.val=answer ∧
      out.steps≤stablePadBudget (a m) (K m) (printedHalf m) (printedRankWidth m)+
        legalRootBudget (J6SourcePrecision.printed m base) (printedFactorWidth m n) (printedAnswerWidth m base)
          ell frame.words.length (printedRankWidth m-a m+13*a m) m pads+8+gatherCost frame m sites := by
  let sites := rawOuterSite D S pad B R sync reserved frame hv
  let slots (i : Centre) := (slotRead frame m sites i).result
  let fit := printed_readout_fits m n base (constantRootWord m)
  let O := outerOracle D S pad B R sync reserved frame hv
  have hF : 0<f.natDegree := frame.natDegree D.hf ▸ frame.sizePos
  have truth (i : Centre) :
      frame.decode (slots i)=
        (polynomial
          (stableRootPacking m (printedHalf m) n (printedRankWidth m) P (constantRootWord m)
            G.room G.half G.rankA G.rankFit.le)
          (oddAxis m) (index m i:ℤ) (J6SourcePrecision.printed m base)
          (rootEntryFile f ell base P (constantRootWord m)) D.hf).eval 0 := by
    change frame.decode (slotRead frame m sites i).result=_
    rw [(stored_slot_exact frame m sites i).1]
    have exactSite := each_outer_site_pays_the_actual_public_replies_once D S pad B R sync reserved frame hv i
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

#print axioms runRawOuterCount
#print axioms exact_guarded_count_from_the_actual_outer_runs
end
end J6R75OuterTime

