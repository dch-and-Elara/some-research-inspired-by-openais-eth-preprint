import J6R75OuterTimeBounds
import J6R75OuterTimeCoreCap

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 5000
set_option maxHeartbeats 26000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

/-! Same meter from original request-image compilation through every
actual literal R57/R68 group to the final signed extraction. The
R68 numerical guards and measured driver/start/install budgets remain
explicit; no fee from another run substitutes for a local one. -/
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

variable (W : Widths m native tc tj tw edgew)
variable (I : SharedInputs G ell q rr cc dd prec kp bw)
variable (pad : ℕ)
variable (B : PageBank f ell (KeyWidth kp tc tj) prec tw bw (pageKeyWidth m+pad))
variable {s C rate cw : ℕ} {cfg : RootBounds s C f}
variable (driver : (image : RequestImage W I) →
  Meter (RawGroupPlans image.compiled image.tables pad B cfg rate cw))
variable (sync : B.synced)
variable (reserve : ∀ image : RequestImage W I,
  ∀ x∈B.headers,x.id.bits.take kp≠image.compiled.mark.bits)

theorem whole_compiled_literal_run_has_the_exact_count_and_charge
    (install core : ℕ)
    (payInstall : let I0 := (buildRequestImage W I).result
      ∀ (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64),
        ((cachedExteriorJob I0.compiled I0.tables pad
          (sourceRow (W:=W) I0.compiled i j g)).install B).steps ≤ install)
    (payCore : let I0 := (buildRequestImage W I).result
      ∀ (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64),
        (coreRawGroup I0.compiled I0.tables pad B (driver I0).result i j g).steps ≤ core)
    (positiveBase : 0<base) (zeroOpening : coreA P (fun _=>false)=true)
    (answer : ℕ) (count : Nat.card {x : Fin m→Bool // coreA P x=true ∧ coreB P x=true}=1+answer) :
    let J := buildRequestImage W I
    let F := J.result.compiled.frame
    let pads := (exactPadOrder m (K m) (printedHalf m) (constantRootWord m)).length
    let p := J6SourcePrecision.printed m base
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
  let D := J.result.compiled
  let found := (driver J.result).result
  let q0 := physicalSlotRoof m native tc tj tw kp f.natDegree (J6SourcePrecision.printed m base) ell install core
  have each (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) :
      (paidRawSlot D J.result.tables pad B found sync (reserve J.result) D.frame D.positive i j
        (J.result.tables.requests.probes.read j).result.val).steps ≤ q0 :=
    each_public_slot_has_a_numeric_roof D J.result.tables pad B found sync (reserve J.result)
      D.frame D.positive install core payInstall payCore i j _
  have bound := whole_prescribed_outer_count_has_measured_time D J.result.tables pad B found
    sync (reserve J.result) D.frame D.positive q0 each positiveBase zeroOpening answer count
  dsimp only
  rw [one_actual_compilation_and_extraction_fee W I pad B driver sync reserve]
  exact ⟨bound.1,Nat.add_le_add_right (Nat.add_le_add_left bound.2 _) _⟩

theorem whole_compiled_literal_run_uses_the_absolute_phase_rate
    (install fixed arithmetic perScope scale localPower : ℕ)
    (payPublic : let I0 := (buildRequestImage W I).result
      ∀ (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64),
        let r := sourceRow (W:=W) I0.compiled i j g
        let job := cachedExteriorJob I0.compiled I0.tables pad r
        publishFee B job.entry job.offset job.built ≤ install)
    (observed : let I0 := (buildRequestImage W I).result
      ∀ (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64),
        actualGroupPhaseCaps I0.compiled I0.tables pad B (driver I0).result i j g fixed arithmetic perScope)
    (numeric : fixed+(arithmetic+perScope) ≤ scale*2^(localPower*J9PrintedSchedule.leafThreshold s (Nat.clog 2 s)))
    (positiveBase : 0<base) (zeroOpening : coreA P (fun _=>false)=true)
    (answer : ℕ) (count : Nat.card {x : Fin m→Bool // coreA P x=true ∧ coreB P x=true}=1+answer) :
    let J := buildRequestImage W I
    let F := J.result.compiled.frame
    let pads := (exactPadOrder m (K m) (printedHalf m) (constantRootWord m)).length
    let p := J6SourcePrecision.printed m base
    let core := uniformRawExteriorRoof s C scale localPower
    let q0 := physicalSlotRoof m native tc tj tw kp f.natDegree p ell install core
    let site := rootSiteFee f.natDegree m (literalDegree m native) ell p F.hp+(literalDegree m native+1)*q0
    let out := compileThenRawOuterCount W I pad B driver sync reserve
    bitsValue out.result.val=answer ∧
    out.steps ≤ J.steps+(driver J.result).steps+
      (stablePadBudget (a m) (K m) (printedHalf m) (printedRankWidth m)+
        legalRootBudget p (printedFactorWidth m n) (printedAnswerWidth m base)
          ell F.words.length (printedRankWidth m-a m+13*a m) m pads+8+
        gatheredOracleFee m F.words.length ell p site)+5 := by
  let I0 := (buildRequestImage W I).result
  let D := I0.compiled
  let R := (driver I0).result
  have pub (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64) :
      ((cachedExteriorJob D I0.tables pad (sourceRow (W:=W) D i j g)).install B).steps ≤ install := by
    rw [literal_outer_publication_is_the_true_publish_fee D I0.tables pad B i j g sync (reserve I0)]
    exact payPublic i j g
  have run (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64) :
      (coreRawGroup D I0.tables pad B R i j g).steps ≤ uniformRawExteriorRoof s C scale localPower :=
    the_group_uses_the_actual_absolute_depth_tariff D I0.tables pad B R i j g fixed arithmetic perScope scale localPower
      (observed i j g) numeric
  exact whole_compiled_literal_run_has_the_exact_count_and_charge W I pad B driver sync reserve
    install (uniformRawExteriorRoof s C scale localPower) pub run positiveBase zeroOpening answer count

#print axioms whole_compiled_literal_run_has_the_exact_count_and_charge
#print axioms whole_compiled_literal_run_uses_the_absolute_phase_rate
end
end J6R75OuterTime

