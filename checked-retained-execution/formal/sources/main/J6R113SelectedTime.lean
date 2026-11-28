import J6R112ExecutedSelectedStartupPlan
import J6R107ActualOuter

/-! Derive the raw clock on precisely the selected request image and
recursive plans. Use the original numeric interpolation bound and add
the setup bills of the executed selected continuation. -/
namespace J6R113SelectedTime
open scoped Classical Polynomial BigOperators
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
open J6R102FinalPhase J6R106OuterBudget J6R112ExecutedSelectedStartup
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 4900
set_option maxHeartbeats 22000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

noncomputable section
variable {V : Type} [Fintype V] {m n base native : ℕ} {f : ℤ[X]} {P : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) P (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable {W : Widths m native tc tj tw edgew} {I : SharedInputs G ell q rr cc dd prec kp bw}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (image : RequestImage W I) (plan : SelectedCountOnImage image)
variable (K0 producerPower leafPower : ℕ) (coefficients : ProducerCoefficients)

def sameImageRawClock : ℕ :=
  let F := image.compiled.frame
  let pads := (exactPadOrder m (K m) (printedHalf m) (constantRootWord m)).length
  let p := J6SourcePrecision.printed m base
  let install := selectedPublicationClock image.compiled image.tables plan.pad plan.prior
  let core := uniformRawExteriorRoof plan.size plan.constant
    (3*sourceCoefficient K0 coefficients) (printedLocalExponent producerPower leafPower)
  let q0 := physicalSlotRoof m native tc tj tw kp f.natDegree p ell install core
  let site := rootSiteFee f.natDegree m (literalDegree m native) ell p F.hp+
    (literalDegree m native+1)*q0
  stablePadBudget (a m) (K m) (printedHalf m) (printedRankWidth m)+
    legalRootBudget p (printedFactorWidth m n) (printedAnswerWidth m base)
      ell F.words.length (printedRankWidth m-a m+13*a m) m pads+8+
    gatheredOracleFee m F.words.length ell p site

theorem reindexing_the_plan_width_keeps_the_same_core_charge
    {a b : ℕ} (eq : a=b)
    (R : RawGroupPlans image.compiled image.tables plan.pad plan.prior plan.bounds plan.rate a)
    (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64) :
    (coreRawGroup image.compiled image.tables plan.pad plan.prior (eq ▸ R) i j g).steps=
      (coreRawGroup image.compiled image.tables plan.pad plan.prior R i j g).steps := by
  subst b
  rfl

theorem actual_selected_image_uses_its_source_clock_and_bills_its_setups
    (rank : ℕ) (rankEq : plan.rankWidth=rank+1)
    (profile : let R : RawGroupPlans image.compiled image.tables plan.pad plan.prior plan.bounds plan.rate (rank+1) := rankEq ▸ plan.plans
      ∀ (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64),
        Nonempty (SelectedPlanSource image.compiled image.tables plan.pad plan.prior
          (sourceRow (W:=W) image.compiled i j g) (R i j g)
          K0 producerPower leafPower coefficients))
    (positiveBase : 0<base) (zeroOpening : coreA P (fun _=>false)=true)
    (answer : ℕ) (count : Nat.card {x : Fin m→Bool // coreA P x=true ∧ coreB P x=true}=1+answer) :
    (bitsValue (countOnThatImage image plan).result.val=answer) ∧
    (countOnThatImage image plan).steps ≤ sameImageRawClock image plan K0 producerPower leafPower coefficients+
      paidSetupsOnThatImage image plan := by
  let D := image.compiled
  let S := image.tables
  let R := plan.plans
  let B := plan.prior
  let R1 : RawGroupPlans D S plan.pad B plan.bounds plan.rate (rank+1) := rankEq ▸ R
  let install := selectedPublicationClock D S plan.pad B
  let L := localClock plan.size K0 producerPower leafPower coefficients
  let core := uniformRawExteriorRoof plan.size plan.constant (3*sourceCoefficient K0 coefficients)
    (printedLocalExponent producerPower leafPower)
  let p := J6SourcePrecision.printed m base
  let q0 := physicalSlotRoof m native tc tj tw kp f.natDegree p ell install core
  have q (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64) :
      ((cachedExteriorJob D S plan.pad (sourceRow (W:=W) D i j g)).install B).steps ≤ install := by
    rw [literal_outer_publication_is_the_true_publish_fee D S plan.pad B i j g plan.sync plan.reserved]
    exact compiled_publication_obeys_one_real_bank_clock D S plan.pad B (sourceRow (W:=W) D i j g)
  have x (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64) :
      (coreRawGroup D S plan.pad B R i j g).steps ≤ core := by
    obtain ⟨h⟩ := profile i j g
    have R0 : actualGroupPhaseCaps D S plan.pad B R1 i j g L L L :=
      selected_plan_has_the_derived_clock D S plan.pad B (sourceRow (W:=W) D i j g) (R1 i j g)
        K0 producerPower leafPower coefficients h
    have n := (three_uniform_debits_have_the_original_exponent plan.size
      K0 producerPower leafPower coefficients).le
    rw [←reindexing_the_plan_width_keeps_the_same_core_charge image plan rankEq R i j g]
    exact the_group_uses_the_actual_absolute_depth_tariff D S plan.pad B R1 i j g L L L
      (3*sourceCoefficient K0 coefficients) (printedLocalExponent producerPower leafPower) R0 n
  have each (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) :
      (paidRawSlot D S plan.pad B R plan.sync plan.reserved D.frame D.positive i j
        (S.requests.probes.read j).result.val).steps ≤ q0 :=
    each_public_slot_has_a_numeric_roof D S plan.pad B R plan.sync plan.reserved
      D.frame D.positive install core q x i j _
  have old := whole_prescribed_outer_count_has_measured_time D S plan.pad B R plan.sync plan.reserved
    D.frame D.positive q0 each positiveBase zeroOpening answer count
  have new := the_selected_image_count_pays_its_actual_setups image plan
  refine ⟨?_,?_⟩
  · rw [new.value]
    exact old.1
  · rw [new.fee]
    exact Nat.add_le_add_right old.2 _

#print axioms actual_selected_image_uses_its_source_clock_and_bills_its_setups
end
end J6R113SelectedTime
