import J6R116PhysicalRetainedImage
import J6R117ReceiptSlotClock

/-! Assembly over the one returned request image. For each real group
address, the preparer takes the actual held payload; the original
addresses index the result, not a second evaluation. -/
namespace J6R114PrescribedReceipts
open scoped Polynomial Classical
open Polynomial AOracleMachineTime AOracleMachineTimeTape A1R10
open J6Mesh J6OrientedHost J6OrientedHostEval J6R51Ingress
open J6R54PublicFamily J6R57PublicRequest J6R27PrescribedProbe J6R28GeneratedRootFrame
open J6R22RootReadout J6R75OuterTime J6R36SharedGateway J6R33OriginalJ6 J6R34OfficialGateway
open J6R25StableCensus J6R15ModeCost J6R11Repack J6R24MeteredRecursion
open J6R24LegalLayout J6R26StablePreparedRoot J6R31RootResidentTables J1PPrinted
open J6R14ZeroMode J6R19Retained J6R12Blueprint J6R33StatefulArithmeticPage
open J6R34RootAtlas J6R50SourceProducer J6R52FreshExterior J6R111KeptOwnerFlow

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxRecDepth 5200
set_option maxHeartbeats 15000000
set_option maxSynthPendingDepth 10

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew} {I : SharedInputs G ell q rr cc dd prec kp bw}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]


variable (image : RequestImage W I) (Q : PhysicalRetainedImagePlan image)

open J6R75OuterTime J6R34OfficialGateway J6R35GatewayPreparation
open J6R33OriginalJ6 J6R25StableCensus J6R22RootReadout J6R11Repack
open J6R14ZeroMode J1PPrinted J6R14LayoutCost J6R36SharedGateway

abbrev actualSameImageReceipts : ActualGroupReceipts (W:=W) image.compiled :=
  addressedPaidReceipts image.compiled image.tables (physicalRowsOnThatImage image Q)

theorem exact_same_physical_count_and_outer_clock
    (groupCap : ℕ)
    (cap : ∀ (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64),
      (actualSameImageReceipts image Q i j g (prepareHead W i j).result rfl).run.steps≤groupCap)
    (positiveBase : 0<base) (zeroOpening : coreA P (fun _=>false)=true)
    (answer : ℕ) (count : Nat.card {x : Fin m→Bool // coreA P x=true ∧ coreB P x=true}=1+answer) :
    let D := image.compiled
    let frame := D.frame
    let out := runPhysicalRetainedCountAtImage image Q
    let slots := actualReceiptSlotRoof (m:=m) (native:=native) (tc:=tc) (tj:=tj) (tw:=tw)
      (f:=f) (base:=base) (ell:=ell) groupCap
    let pads := (exactPadOrder m (K m) (printedHalf m) (constantRootWord m)).length
    let site := rootSiteFee f.natDegree m (literalDegree m native) ell (J6SourcePrecision.printed m base) frame.hp+
        (literalDegree m native+1)*slots
    bitsValue out.result.val=answer ∧
      out.steps≤stablePadBudget (a m) (K m) (printedHalf m) (printedRankWidth m)+
        legalRootBudget (J6SourcePrecision.printed m base) (printedFactorWidth m n) (printedAnswerWidth m base)
           ell frame.words.length (printedRankWidth m-a m+13*a m) m pads+8+
            gatheredOracleFee m frame.words.length ell (J6SourcePrecision.printed m base) site := by
  let D := image.compiled
  let frame := D.frame
  let R := actualSameImageReceipts image Q
  let slots := actualReceiptSlotRoof (m:=m) (native:=native) (tc:=tc) (tj:=tj) (tw:=tw)
    (f:=f) (base:=base) (ell:=ell) groupCap
  exact the_guarded_count_has_the_clock_of_the_actual_admitted_receipts (W:=W) D image.tables
    frame D.positive R slots (fun i j=>
      the_same_outer_slots_cost_their_actual_groups_and_arithmetic (W:=W) D frame D.positive R groupCap cap
        i j (image.tables.requests.probes.read j).result.val)
    positiveBase zeroOpening answer count

#print axioms exact_same_physical_count_and_outer_clock
end
end J6R114PrescribedReceipts

