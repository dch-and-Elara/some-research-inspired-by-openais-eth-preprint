import J6R102FinalPhaseOuter
import J6R106OuterBudget

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 5000
set_option maxHeartbeats 26000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! The selected compiled count has no extra supplied publication bound.
The publication roof prices the actual shared atlas and directory. -/
namespace J6R107ActualOuter
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
open J6R63Active J6R62ActivePrep J6R14ZeroMode J6R75OuterTime J6R79Numeric

open J6R102FinalPhase J6R106OuterBudget

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]

variable (W : Widths m native tc tj tw edgew)
variable (I : SharedInputs G ell q rr cc dd prec kp bw)
variable (pad : ℕ)
variable (B : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
variable {s C rate rank : ℕ} {cfg : RootBounds s C f}
variable (driver : (image : RequestImage W I) →
  Meter (RawGroupPlans image.compiled image.tables pad B cfg rate (rank+1)))
variable (sync : B.synced)
variable (reserve : ∀ image : RequestImage W I,
  ∀ x∈B.headers,x.id.bits.take kp≠image.compiled.mark.bits)

theorem actual_outer_time_with_derived_publication_clock
    (Wbudget producerPower leafPower : ℕ) (coefficients : ProducerCoefficients)
    (producerProfiles : let I0 := (buildRequestImage W I).result
      ∀ (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64),
        Nonempty (SelectedPlanSource I0.compiled I0.tables pad B (sourceRow (W:=W) I0.compiled i j g)
          ((driver I0).result i j g) Wbudget producerPower leafPower coefficients))
    (positiveBase : 0<base) (zeroOpening : coreA P (fun _=>false)=true)
    (answer : ℕ) (count : Nat.card {x : Fin m→Bool // coreA P x=true ∧ coreB P x=true}=1+answer) :
    let J := buildRequestImage W I
    let install := selectedPublicationClock J.result.compiled J.result.tables pad B
    let F := J.result.compiled.frame
    let pads := (exactPadOrder m (K m) (printedHalf m) (constantRootWord m)).length
    let p := J6SourcePrecision.printed m base
    let core := uniformRawExteriorRoof s C (3*sourceCoefficient Wbudget coefficients) (printedLocalExponent producerPower leafPower)
    let q0 := physicalSlotRoof m native tc tj tw kp f.natDegree p ell install core
    let site := rootSiteFee f.natDegree m (literalDegree m native) ell p F.hp+(literalDegree m native+1)*q0
    let out := compileThenRawOuterCount W I pad B driver sync reserve
    bitsValue out.result.val=answer ∧
    out.steps ≤ J.steps+(driver J.result).steps+
      (stablePadBudget (a m) (K m) (printedHalf m) (printedRankWidth m)+
        legalRootBudget p (printedFactorWidth m n) (printedAnswerWidth m base)
          ell F.words.length (printedRankWidth m-a m+13*a m) m pads+8+
        gatheredOracleFee m F.words.length ell p site)+5 := by
  let J := buildRequestImage W I
  let install := selectedPublicationClock J.result.compiled J.result.tables pad B
  have published (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64) :
      let r := sourceRow (W:=W) J.result.compiled i j g
      let job := cachedExteriorJob J.result.compiled J.result.tables pad r
      publishFee B job.entry job.offset job.built ≤ install :=
    compiled_publication_obeys_one_real_bank_clock J.result.compiled J.result.tables pad B
      (sourceRow (W:=W) J.result.compiled i j g)
  exact actual_compiled_outer_time_from_the_chosen_producer_profiles W I pad B driver sync reserve
    install Wbudget producerPower leafPower coefficients published producerProfiles
    positiveBase zeroOpening answer count

#print axioms actual_outer_time_with_derived_publication_clock
end
end J6R107ActualOuter

